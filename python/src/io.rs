#![allow(clippy::needless_option_as_deref)]

use crate::model::{PyQuad, PyTriple};
use oxigraph::io::{FromReadQuadReader, ParseError, RdfFormat, RdfParser, RdfSerializer};
use oxigraph::model::QuadRef;
use pyo3::exceptions::{PySyntaxError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use pyo3::{intern, wrap_pyfunction};
use std::cmp::max;
use std::error::Error;
use std::fs::File;
use std::io::{self, BufWriter, Cursor, Read, Write};
use std::path::{Path, PathBuf};

pub fn add_to_module(module: &PyModule) -> PyResult<()> {
    module.add_wrapped(wrap_pyfunction!(parse))?;
    module.add_wrapped(wrap_pyfunction!(serialize))
}

/// Parses RDF graph and dataset serialization formats.
///
/// It currently supports the following formats:
///
/// * `N-Triples <https://www.w3.org/TR/n-triples/>`_ (``application/n-triples``)
/// * `N-Quads <https://www.w3.org/TR/n-quads/>`_ (``application/n-quads``)
/// * `Turtle <https://www.w3.org/TR/turtle/>`_ (``text/turtle``)
/// * `TriG <https://www.w3.org/TR/trig/>`_ (``application/trig``)
/// * `RDF/XML <https://www.w3.org/TR/rdf-syntax-grammar/>`_ (``application/rdf+xml``)
///
/// It supports also some MIME type aliases.
/// For example, ``application/turtle`` could also be used for `Turtle <https://www.w3.org/TR/turtle/>`_
/// and ``application/xml`` for `RDF/XML <https://www.w3.org/TR/rdf-syntax-grammar/>`_.
///
/// :param input: The binary I/O object or file path to read from. For example, it could be a file path as a string or a file reader opened in binary mode with ``open('my_file.ttl', 'rb')``.
/// :type input: io(bytes) or io(str) or str or pathlib.Path
/// :param mime_type: the MIME type of the RDF serialization.
/// :type mime_type: str
/// :param base_iri: the base IRI used to resolve the relative IRIs in the file or :py:const:`None` if relative IRI resolution should not be done.
/// :type base_iri: str or None, optional
/// :param without_named_graphs: Sets that the parser must fail if parsing a named graph.
/// :type without_named_graphs: bool, optional
/// :param rename_blank_nodes: Renames the blank nodes ids from the ones set in the serialization to random ids. This allows to avoid id conflicts when merging graphs together.
/// :type rename_blank_nodes: bool, optional
/// :return: an iterator of RDF triples or quads depending on the format.
/// :rtype: iterator(Quad)
/// :raises ValueError: if the MIME type is not supported.
/// :raises SyntaxError: if the provided data is invalid.
///
/// >>> input = io.BytesIO(b'<foo> <p> "1" .')
/// >>> list(parse(input, "text/turtle", base_iri="http://example.com/"))
/// [<Quad subject=<NamedNode value=http://example.com/foo> predicate=<NamedNode value=http://example.com/p> object=<Literal value=1 datatype=<NamedNode value=http://www.w3.org/2001/XMLSchema#string>> graph_name=<DefaultGraph>>]
#[pyfunction]
#[pyo3(signature = (input, mime_type, *, base_iri = None, without_named_graphs = false, rename_blank_nodes = false))]
pub fn parse(
    input: PyObject,
    mime_type: &str,
    base_iri: Option<&str>,
    without_named_graphs: bool,
    rename_blank_nodes: bool,
    py: Python<'_>,
) -> PyResult<PyObject> {
    let Some(format) = RdfFormat::from_media_type(mime_type) else {
        return Err(PyValueError::new_err(format!(
            "Not supported MIME type: {mime_type}"
        )));
    };
    let input = if let Ok(path) = input.extract::<PathBuf>(py) {
        PyReadable::from_file(&path, py).map_err(map_io_err)?
    } else {
        PyReadable::from_data(input, py)
    };
    let mut parser = RdfParser::from_format(format);
    if let Some(base_iri) = base_iri {
        parser = parser
            .with_base_iri(base_iri)
            .map_err(|e| PyValueError::new_err(e.to_string()))?;
    }
    if without_named_graphs {
        parser = parser.without_named_graphs();
    }
    if rename_blank_nodes {
        parser = parser.rename_blank_nodes();
    }
    Ok(PyQuadReader {
        inner: parser.parse_read(input),
    }
    .into_py(py))
}

/// Serializes an RDF graph or dataset.
///
/// It currently supports the following formats:
///
/// * `N-Triples <https://www.w3.org/TR/n-triples/>`_ (``application/n-triples``)
/// * `N-Quads <https://www.w3.org/TR/n-quads/>`_ (``application/n-quads``)
/// * `Turtle <https://www.w3.org/TR/turtle/>`_ (``text/turtle``)
/// * `TriG <https://www.w3.org/TR/trig/>`_ (``application/trig``)
/// * `RDF/XML <https://www.w3.org/TR/rdf-syntax-grammar/>`_ (``application/rdf+xml``)
///
/// It supports also some MIME type aliases.
/// For example, ``application/turtle`` could also be used for `Turtle <https://www.w3.org/TR/turtle/>`_
/// and ``application/xml`` for `RDF/XML <https://www.w3.org/TR/rdf-syntax-grammar/>`_.
///
/// :param input: the RDF triples and quads to serialize.
/// :type input: iterable(Triple) or iterable(Quad)
/// :param output: The binary I/O object or file path to write to. For example, it could be a file path as a string or a file writer opened in binary mode with ``open('my_file.ttl', 'wb')``.
/// :type output: io(bytes) or str or pathlib.Path
/// :param mime_type: the MIME type of the RDF serialization.
/// :type mime_type: str
/// :rtype: None
/// :raises ValueError: if the MIME type is not supported.
/// :raises TypeError: if a triple is given during a quad format serialization or reverse.
///
/// >>> output = io.BytesIO()
/// >>> serialize([Triple(NamedNode('http://example.com'), NamedNode('http://example.com/p'), Literal('1'))], output, "text/turtle")
/// >>> output.getvalue()
/// b'<http://example.com> <http://example.com/p> "1" .\n'
#[pyfunction]
pub fn serialize(input: &PyAny, output: PyObject, mime_type: &str, py: Python<'_>) -> PyResult<()> {
    let Some(format) = RdfFormat::from_media_type(mime_type) else {
        return Err(PyValueError::new_err(format!(
            "Not supported MIME type: {mime_type}"
        )));
    };
    let output = if let Ok(path) = output.extract::<PathBuf>(py) {
        PyWritable::from_file(&path, py).map_err(map_io_err)?
    } else {
        PyWritable::from_data(output)
    };
    let mut writer = RdfSerializer::from_format(format).serialize_to_write(BufWriter::new(output));
    for i in input.iter()? {
        let i = i?;
        if let Ok(triple) = i.extract::<PyRef<PyTriple>>() {
            writer.write_triple(&*triple)
        } else {
            let quad = i.extract::<PyRef<PyQuad>>()?;
            let quad = QuadRef::from(&*quad);
            if !quad.graph_name.is_default_graph() && !format.supports_datasets() {
                return Err(PyValueError::new_err(
                    "The {format} format does not support named graphs",
                ));
            }
            writer.write_quad(quad)
        }
        .map_err(map_io_err)?;
    }
    writer
        .finish()
        .map_err(map_io_err)?
        .into_inner()
        .map_err(|e| map_io_err(e.into_error()))?
        .close()
        .map_err(map_io_err)
}

#[pyclass(name = "QuadReader", module = "pyoxigraph")]
pub struct PyQuadReader {
    inner: FromReadQuadReader<PyReadable>,
}

#[pymethods]
impl PyQuadReader {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<Self> {
        slf
    }

    fn __next__(&mut self, py: Python<'_>) -> PyResult<Option<PyQuad>> {
        py.allow_threads(|| {
            self.inner
                .next()
                .map(|q| Ok(q.map_err(map_parse_error)?.into()))
                .transpose()
        })
    }
}

pub enum PyReadable {
    Bytes(Cursor<Vec<u8>>),
    Io(PyIo),
    File(File),
}

impl PyReadable {
    pub fn from_file(file: &Path, py: Python<'_>) -> io::Result<Self> {
        Ok(Self::File(py.allow_threads(|| File::open(file))?))
    }

    pub fn from_data(data: PyObject, py: Python<'_>) -> Self {
        if let Ok(bytes) = data.extract::<Vec<u8>>(py) {
            Self::Bytes(Cursor::new(bytes))
        } else if let Ok(string) = data.extract::<String>(py) {
            Self::Bytes(Cursor::new(string.into_bytes()))
        } else {
            Self::Io(PyIo(data))
        }
    }
}

impl Read for PyReadable {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Bytes(bytes) => bytes.read(buf),
            Self::Io(io) => io.read(buf),
            Self::File(file) => file.read(buf),
        }
    }
}

pub enum PyWritable {
    Io(PyIo),
    File(File),
}

impl PyWritable {
    pub fn from_file(file: &Path, py: Python<'_>) -> io::Result<Self> {
        Ok(Self::File(py.allow_threads(|| File::create(file))?))
    }

    pub fn from_data(data: PyObject) -> Self {
        Self::Io(PyIo(data))
    }

    pub fn close(mut self) -> io::Result<()> {
        self.flush()?;
        if let Self::File(file) = self {
            file.sync_all()?;
        }
        Ok(())
    }
}

impl Write for PyWritable {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Io(io) => io.write(buf),
            Self::File(file) => file.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Io(io) => io.flush(),
            Self::File(file) => file.flush(),
        }
    }
}

pub struct PyIo(PyObject);

impl Read for PyIo {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        Python::with_gil(|py| {
            if buf.is_empty() {
                return Ok(0);
            }
            let to_read = max(1, buf.len() / 4); // We divide by 4 because TextIO works with number of characters and not with number of bytes
            let read = self
                .0
                .as_ref(py)
                .call_method1(intern!(py, "read"), (to_read,))
                .map_err(to_io_err)?;
            let bytes = read
                .extract::<&[u8]>()
                .or_else(|e| read.extract::<&str>().map(str::as_bytes).map_err(|_| e))
                .map_err(to_io_err)?;
            buf[..bytes.len()].copy_from_slice(bytes);
            Ok(bytes.len())
        })
    }
}

impl Write for PyIo {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        Python::with_gil(|py| {
            self.0
                .as_ref(py)
                .call_method1(intern!(py, "write"), (PyBytes::new(py, buf),))
                .map_err(to_io_err)?
                .extract::<usize>()
                .map_err(to_io_err)
        })
    }

    fn flush(&mut self) -> io::Result<()> {
        Python::with_gil(|py| {
            self.0
                .as_ref(py)
                .call_method0(intern!(py, "flush"))
                .map_err(to_io_err)?;
            Ok(())
        })
    }
}

fn to_io_err(error: PyErr) -> io::Error {
    io::Error::new(io::ErrorKind::Other, error)
}

pub fn map_io_err(error: io::Error) -> PyErr {
    if error
        .get_ref()
        .map_or(false, <(dyn Error + Send + Sync + 'static)>::is::<PyErr>)
    {
        *error.into_inner().unwrap().downcast().unwrap()
    } else {
        error.into()
    }
}

pub fn map_parse_error(error: ParseError) -> PyErr {
    match error {
        ParseError::Syntax(error) => PySyntaxError::new_err(error.to_string()),
        ParseError::Io(error) => map_io_err(error),
    }
}

/// Release the GIL
/// There should not be ANY use of pyo3 code inside of this method!!!
///
/// Code from pyo3: https://github.com/PyO3/pyo3/blob/a67180c8a42a0bc0fdc45b651b62c0644130cf47/src/python.rs#L366
#[allow(unsafe_code)]
pub fn allow_threads_unsafe<T>(f: impl FnOnce() -> T) -> T {
    struct RestoreGuard {
        tstate: *mut pyo3::ffi::PyThreadState,
    }

    impl Drop for RestoreGuard {
        fn drop(&mut self) {
            unsafe {
                pyo3::ffi::PyEval_RestoreThread(self.tstate);
            }
        }
    }

    let _guard = RestoreGuard {
        tstate: unsafe { pyo3::ffi::PyEval_SaveThread() },
    };
    f()
}
