use oxigraph::sparql::dataset::HDTDatasetView;
use oxigraph::sparql::evaluate_hdt_query;
use oxigraph::sparql::QueryOptions;
use oxigraph::sparql::QueryResults;
use std::rc::Rc;

// Run with `cargo run --bin hdt_driver`.

// Based on oxigraph/lib/README.md, https://w3c.github.io/rdf-tests/,
// and https://www.w3.org/TR/sparql11-query/#WritingSimpleQueries.

fn main() {
    println!("Oxigraph/HDT - Driver for Testing");

    // Open the HDT file.
    let dataset = Rc::new(HDTDatasetView::new("hdt_driver/test.hdt"));

    // Test
    println!();
    println!("Test");
    println!();

    let sparql_query = "SELECT ?o WHERE { <http://example.org/book/book1> ?p ?o }";

    let (results, _explain) = evaluate_hdt_query(
        Rc::clone(&dataset),
        sparql_query,
        QueryOptions::default(),
        false,
    )
    .expect("failed to evaluate SPARQL query");

    if let QueryResults::Solutions(solutions) = results.unwrap() {
        for solution in solutions {
            println!("{}", solution.unwrap().get("o").unwrap());
        }
    }

    // Test
    println!();
    println!("Test");
    println!();

    let sparql_query = "SELECT ?s WHERE { ?s <http://purl.org/dc/elements/1.1/title> ?o }";

    let (results, _explain) = evaluate_hdt_query(
        Rc::clone(&dataset),
        sparql_query,
        QueryOptions::default(),
        false,
    )
    .expect("failed to evaluate SPARQL query");

    if let QueryResults::Solutions(solutions) = results.unwrap() {
        for solution in solutions {
            println!("{}", solution.unwrap().get("s").unwrap());
        }
    }

    // Test
    println!();
    println!("Test");
    println!();

    let sparql_query = "SELECT ?s ?p ?o WHERE { <http://example.org/book/book1> ?p ?o . ?s ?p \"SPARQL Tutorial\" }";

    let (results, _explain) = evaluate_hdt_query(
        Rc::clone(&dataset),
        sparql_query,
        QueryOptions::default(),
        false,
    )
    .expect("failed to evaluate SPARQL query");

    if let QueryResults::Solutions(solutions) = results.unwrap() {
        for solution in solutions {
            let bindings = solution.unwrap();
            println!("{}", &bindings.get("s").unwrap());
            println!("{}", &bindings.get("p").unwrap());
            println!("{}", &bindings.get("o").unwrap());
        }
    }
}
