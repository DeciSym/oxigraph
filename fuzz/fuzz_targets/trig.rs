#![no_main]

use libfuzzer_sys::fuzz_target;
use oxigraph_fuzz::count_quad_blank_nodes;
use oxrdf::graph::CanonicalizationAlgorithm;
use oxrdf::{Dataset, Quad};
use oxttl::{TriGParser, TriGSerializer};

fn parse<'a>(
    chunks: impl IntoIterator<Item = &'a [u8]>,
    unchecked: bool,
) -> (Vec<Quad>, Vec<String>, Vec<(String, String)>) {
    let mut quads = Vec::new();
    let mut errors = Vec::new();
    let mut parser = TriGParser::new()
        .with_quoted_triples()
        .with_base_iri("http://example.com/")
        .unwrap();
    if unchecked {
        parser = parser.unchecked();
    }
    let mut parser = parser.low_level();
    for chunk in chunks {
        parser.extend_from_slice(chunk);
        while let Some(result) = parser.parse_next() {
            match result {
                Ok(quad) => quads.push(quad),
                Err(error) => errors.push(error.to_string()),
            }
        }
    }
    parser.end();
    while let Some(result) = parser.parse_next() {
        match result {
            Ok(quad) => quads.push(quad),
            Err(error) => errors.push(error.to_string()),
        }
    }
    assert!(parser.is_end());
    (
        quads,
        errors,
        parser
            .prefixes()
            .map(|(k, v)| (k.to_owned(), v.to_owned()))
            .collect(),
    )
}

fn serialize_quads(quads: &[Quad], prefixes: Vec<(String, String)>) -> Vec<u8> {
    let mut serializer = TriGSerializer::new();
    for (prefix_name, prefix_iri) in prefixes {
        serializer = serializer.with_prefix(prefix_name, prefix_iri).unwrap();
    }
    let mut serializer = serializer.for_writer(Vec::new());
    for quad in quads {
        serializer.serialize_quad(quad).unwrap();
    }
    serializer.finish().unwrap()
}

fuzz_target!(|data: &[u8]| {
    // We parse with splitting
    let (quads, errors, prefixes) = parse(data.split(|c| *c == 0xFF), false);
    // We parse without splitting
    let (quads_without_split, errors_without_split, _) = parse(
        [data
            .iter()
            .copied()
            .filter(|c| *c != 0xFF)
            .collect::<Vec<_>>()
            .as_slice()],
        false,
    );
    let (quads_unchecked, errors_unchecked, _) = parse(data.split(|c| *c == 0xFF), true);
    if errors.is_empty() {
        assert!(errors_unchecked.is_empty());
    }

    let bnodes_count = quads
        .iter()
        .map(|q| count_quad_blank_nodes(q.as_ref()))
        .sum::<usize>();
    if bnodes_count == 0 {
        assert_eq!(
            quads,
            quads_without_split,
            "With split:\n{}\nWithout split:\n{}",
            String::from_utf8_lossy(&serialize_quads(&quads, Vec::new())),
            String::from_utf8_lossy(&serialize_quads(&quads_without_split, Vec::new()))
        );
        if errors.is_empty() {
            assert_eq!(
                quads,
                quads_unchecked,
                "Validating:\n{}\nUnchecked:\n{}",
                String::from_utf8_lossy(&serialize_quads(&quads, Vec::new())),
                String::from_utf8_lossy(&serialize_quads(&quads_unchecked, Vec::new()))
            );
        }
    } else if bnodes_count <= 4 {
        let mut dataset_with_split = quads.iter().collect::<Dataset>();
        let mut dataset_without_split = quads_without_split.iter().collect::<Dataset>();
        dataset_with_split.canonicalize(CanonicalizationAlgorithm::Unstable);
        dataset_without_split.canonicalize(CanonicalizationAlgorithm::Unstable);
        assert_eq!(
            dataset_with_split,
            dataset_without_split,
            "With split:\n{}\nWithout split:\n{}",
            String::from_utf8_lossy(&serialize_quads(&quads, Vec::new())),
            String::from_utf8_lossy(&serialize_quads(&quads_without_split, Vec::new()))
        );
        if errors.is_empty() {
            let mut dataset_unchecked = quads_unchecked.iter().collect::<Dataset>();
            dataset_unchecked.canonicalize(CanonicalizationAlgorithm::Unstable);
            assert_eq!(
                dataset_with_split,
                dataset_unchecked,
                "Validating:\n{}\nUnchecked:\n{}",
                String::from_utf8_lossy(&serialize_quads(&quads, Vec::new())),
                String::from_utf8_lossy(&serialize_quads(&quads_unchecked, Vec::new()))
            );
        }
    }
    assert_eq!(errors, errors_without_split);

    // We serialize
    let new_serialization = serialize_quads(&quads, prefixes);

    // We parse the serialization
    let new_quads = TriGParser::new()
        .with_quoted_triples()
        .for_slice(&new_serialization)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| {
            format!(
                "Error on {:?} from {quads:?} based on {:?}: {e}",
                String::from_utf8_lossy(&new_serialization),
                String::from_utf8_lossy(data)
            )
        })
        .unwrap();

    // We check the roundtrip has not changed anything
    assert_eq!(new_quads, quads);
});
