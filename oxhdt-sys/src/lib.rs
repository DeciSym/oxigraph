#[allow(unused_imports)]
use oxigraph::model::{Literal, NamedNode};
use oxigraph::sparql::dataset::HDTDatasetView;
use oxigraph::sparql::evaluate_hdt_query;
use oxigraph::sparql::EvaluationError;
use oxigraph::sparql::Query;
use oxigraph::sparql::QueryOptions;
use oxigraph::sparql::QueryResults;
use oxigraph_testsuite::sparql_evaluator::{
    are_query_results_isomorphic, load_sparql_query_result, StaticQueryResults,
};
use std::fs;
use std::rc::Rc;

#[allow(dead_code)]
fn hdt_query(hdt_path: &str, sparql_query: &str) -> Result<QueryResults, EvaluationError> {
    // Open the HDT file.
    let dataset = Rc::new(HDTDatasetView::new(vec![hdt_path.to_string()]));
    let sparql_query = sparql_query;

    // SPARQL query
    let (results, _explain) = evaluate_hdt_query(
        Rc::clone(&dataset),
        sparql_query,
        QueryOptions::default(),
        false,
    )
    .expect("failed to evaluate SPARQL query");

    return results;
}

#[allow(dead_code)]
fn rdf_test_runner(query_path: &str, data_path: &str, result_path: &str) -> bool {
    // The test SPARQL query
    let rq = fs::read_to_string(&query_path).expect("Failed to read test query from file");

    let query = Query::parse(&rq, None).expect("Failed to parse the test query string");

    // The test data in HDT format
    let data = Rc::new(HDTDatasetView::new(vec![data_path.to_string()]));

    // The expected results in XML format
    // let f = File::open(result_path).expect("Failed to open the expected results from file");
    // let f = BufReader::new(f);
    // let ref_results = QueryResults::read(f, QueryResultsFormat::Xml);

    // Execute the query
    let (results, _explain) =
        evaluate_hdt_query(Rc::clone(&data), query, QueryOptions::default(), false)
            .expect("Failed to evaluate SPARQL query");

    // Compare the XML results

    // XML result serializations may differ for the same semantics
    // due to whitespace and the order of nodes.

    // Results may differ when a SELECT * wildcard is used since
    // the order of the bindings is undefined.

    // let static_ref_results =
    //     StaticQueryResults::from_query_results(ref_results.unwrap(), false).unwrap();

    // Load the SPARQL query results, automatically identifying the source format.
    let static_ref_results = load_sparql_query_result(&result_path)
        .expect("Failed to load the reference results from file");

    // Set the second parameter, "with_order" to true so that order of
    // results is preserved. This is necessary for the "sort" set of
    // W3C SPARQL 1.0 Query test cases.
    let static_results = StaticQueryResults::from_query_results(results.unwrap(), true)
        .expect("Failed to transorm the calculated results to a static result");

    let results_match = are_query_results_isomorphic(&static_ref_results, &static_results);

    // Debug failures by rerunning the query and printing out the
    // results.
    if !results_match {
        let query2 = Query::parse(&rq, None).unwrap();
        let (results_dbg, _explain) =
            evaluate_hdt_query(Rc::clone(&data), query2, QueryOptions::default(), false)
                .expect("Failed to evaluate SPARQL query");
        if let QueryResults::Solutions(solutions) = results_dbg.unwrap() {
            for row in solutions {
                dbg!(&row);
            }
        }
    }

    return results_match;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hdt_sparql_select_o_literal_by_s_uri() {
        let ex = Literal::new_simple_literal("SPARQL Tutorial");

        if let QueryResults::Solutions(mut solutions) = hdt_query(
            "tests/resources/test.hdt",
            "SELECT ?o WHERE { <http://example.org/book/book1> ?p ?o }",
        )
        .unwrap()
        {
            assert_eq!(
                solutions.next().unwrap().unwrap().get("o"),
                Some(&ex.into())
            );
        }
    }

    #[test]
    fn hdt_sparql_select_s_uri_by_p_uri() {
        let ex = NamedNode::new("http://example.org/book/book1").unwrap();

        if let QueryResults::Solutions(mut solutions) = hdt_query(
            "tests/resources/test.hdt",
            "SELECT ?s WHERE { ?s <http://purl.org/dc/elements/1.1/title> ?o }",
        )
        .unwrap()
        {
            assert_eq!(
                solutions.next().unwrap().unwrap().get("s"),
                Some(&ex.into())
            );
        }
    }

    #[test]
    fn hdt_sparql_select_spo_by_s_uri_and_o_literal() {
        let ex_s = NamedNode::new("http://example.org/book/book1").unwrap();
        let ex_p = NamedNode::new("http://purl.org/dc/elements/1.1/title").unwrap();
        let ex_o = Literal::new_simple_literal("SPARQL Tutorial");

        if let QueryResults::Solutions(mut solutions) = hdt_query(
            "tests/resources/test.hdt",
            "SELECT ?s ?p ?o WHERE { <http://example.org/book/book1> ?p ?o . ?s ?p \"SPARQL Tutorial\" }"
        ).unwrap() {
            let row = solutions.next().unwrap().unwrap();
            assert_eq!(row.get("s"), Some(&ex_s.into()));
            assert_eq!(row.get("p"), Some(&ex_p.into()));
            assert_eq!(row.get("o"), Some(&ex_o.into()));
        }
    }

    // Create W3C SPARQL 1.0 test functions.
    macro_rules! rdf_sparql10_test {
        ($(($group:literal, $name:ident, $query:literal, $data:literal, $result:literal)),*) => {
            $(
                #[test]
                fn $name() {
                    assert!(super::rdf_test_runner(
                        concat!("../testsuite/rdf-tests/sparql/sparql10/", $group, "/", $query),
                        concat!("tests/resources/rdf-tests/sparql/sparql10/", $group, "/", $data),
                        concat!("https://w3c.github.io/rdf-tests/sparql/sparql10/", $group, "/", $result)
                    ));
                }
            )*
        }
    }

    macro_rules! rdf_sparql10_ignore_test {
        ($(($group:literal, $name:ident, $query:literal, $data:literal, $result:literal)),*) => {
            $(
                #[ignore]
                #[test]
                fn $name() {
                    assert!(super::rdf_test_runner(
                        concat!("../testsuite/rdf-tests/sparql/sparql10/", $group, "/", $query),
                        concat!("tests/resources/rdf-tests/sparql/sparql10/", $group, "/", $data),
                        concat!("https://w3c.github.io/rdf-tests/sparql/sparql10/", $group, "/", $result)
                    ));
                }
            )*
        }
    }

    macro_rules! rdf_sparql10_customized_test {
        ($(($group:literal, $name:ident, $query:literal, $data:literal, $result:literal)),*) => {
            $(
                #[test]
                fn $name() {
                    assert!(super::rdf_test_runner(
                        concat!("../testsuite/rdf-tests/sparql/sparql10/", $group, "/", $query),
                        concat!("tests/resources/rdf-tests/sparql/sparql10/", $group, "/", $data),
                        concat!("https://github.com/oxigraph/oxhdt-sys/tests/resources/rdf-tests/sparql/sparql10/", $group, "/", $result)
                    ));
                }
            )*
        }
    }

    // Create test functions for the combinations of input, data, and
    // output from the W3C SPARQL 1.0 Basic test suite. Note that this
    // implementation fails to stay automatically up-to-date with
    // changes in the upstream W3C SPARQL test suite since the list is
    // hard-coded. Processing the manifest.ttl would enable
    // synchronization with the upsteam suite.
    mod basic {
        rdf_sparql10_test! {
            ("basic", base_prefix_1, "base-prefix-1.rq", "data-1.hdt", "base-prefix-1.srx"),
            ("basic", base_prefix_2, "base-prefix-2.rq", "data-1.hdt", "base-prefix-2.srx"),
            ("basic", base_prefix_3, "base-prefix-3.rq", "data-1.hdt", "base-prefix-3.srx"),
            ("basic", base_prefix_4, "base-prefix-4.rq", "data-1.hdt", "base-prefix-4.srx"),
            ("basic", base_prefix_5, "base-prefix-5.rq", "data-1.hdt", "base-prefix-5.srx"),

            ("basic", list_1, "list-1.rq", "data-2.hdt", "list-1.srx"),
            ("basic", list_2, "list-2.rq", "data-2.hdt", "list-2.srx"),
            ("basic", list_3, "list-3.rq", "data-2.hdt", "list-3.srx"),
            ("basic", list_4, "list-4.rq", "data-2.hdt", "list-4.srx"),

            ("basic", quotes_1, "quotes-1.rq", "data-3.hdt", "quotes-1.srx"),
            ("basic", quotes_2, "quotes-2.rq", "data-3.hdt", "quotes-2.srx"),

            // HDT Java (https://github.com/rdfhdt/hdt-java) creates the
            // data-3.hdt from the data-3.ttl correctly. HDT C++ does not
            // per https://github.com/rdfhdt/hdt-cpp/issues/219.
            ("basic", quotes_3, "quotes-3.rq", "data-3.hdt", "quotes-3.srx"),

            ("basic", quotes_4, "quotes-4.rq", "data-3.hdt", "quotes-4.srx"),

            ("basic", term_1, "term-1.rq", "data-4.hdt", "term-1.srx"),
            ("basic", term_2, "term-2.rq", "data-4.hdt", "term-2.srx"),
            ("basic", term_3, "term-3.rq", "data-4.hdt", "term-3.srx"),
            ("basic", term_4, "term-4.rq", "data-4.hdt", "term-4.srx"),
            ("basic", term_5, "term-5.rq", "data-4.hdt", "term-5.srx"),
            ("basic", term_6, "term-6.rq", "data-4.hdt", "term-6.srx"),
            ("basic", term_7, "term-7.rq", "data-4.hdt", "term-7.srx"),
            ("basic", term_8, "term-8.rq", "data-4.hdt", "term-8.srx"),
            ("basic", term_9, "term-9.rq", "data-4.hdt", "term-9.srx"),

            ("basic", var_1, "var-1.rq", "data-5.hdt", "var-1.srx"),
            ("basic", var_2, "var-2.rq", "data-5.hdt", "var-2.srx"),

            ("basic", bgp_no_match, "bgp-no-match.rq", "data-7.hdt", "bgp-no-match.srx"),
            ("basic", spoo_1, "spoo-1.rq", "data-6.hdt", "spoo-1.srx"),

            ("basic", prefix_name_1, "prefix-name-1.rq", "data-6.hdt", "prefix-name-1.srx")
        }
    }

    mod triple_match {
        rdf_sparql10_test! {
            ("triple-match", dawg_triple_pattern_001, "dawg-tp-01.rq", "data-01.hdt", "result-tp-01.ttl"),
            ("triple-match", dawg_triple_pattern_002, "dawg-tp-02.rq", "data-01.hdt", "result-tp-02.ttl"),
            ("triple-match", dawg_triple_pattern_003, "dawg-tp-03.rq", "data-02.hdt", "result-tp-03.ttl"),
            ("triple-match", dawg_triple_pattern_004, "dawg-tp-04.rq", "dawg-data-01.hdt", "result-tp-04.ttl")
        }
    }

    mod open_world {
        rdf_sparql10_ignore_test! {
            // Excluded with "Multiple writing of the same
            // xsd:integer. Our system does strong normalization." per
            // oxigraph/testsuite/tests/sparql.rs
            // sparql10_w3c_query_evaluation_testsuite
            ("open-world", open_eq_01, "open-eq-01.rq", "data-1.hdt", "open-eq-01-result.srx"),

            // Excluded with "We use XSD 1.1 equality on dates." per
            // oxigraph/testsuite/tests/sparql.rs
            // sparql10_w3c_query_evaluation_testsuite
            ("open-world", date_2, "date-2.rq", "data-3.hdt", "date-2-result.srx")
        }

        rdf_sparql10_test! {
            ("open-world", open_eq_02, "open-eq-02.rq", "data-1.hdt", "open-eq-02-result.srx"),
            ("open-world", open_eq_03, "open-eq-03.rq", "data-1.hdt", "open-eq-03-result.srx"),
            ("open-world", open_eq_04, "open-eq-04.rq", "data-1.hdt", "open-eq-04-result.srx"),
            ("open-world", open_eq_05, "open-eq-05.rq", "data-1.hdt", "open-eq-05-result.srx"),
            ("open-world", open_eq_06, "open-eq-06.rq", "data-1.hdt", "open-eq-06-result.srx"),
            ("open-world", open_eq_07, "open-eq-07.rq", "data-2.hdt", "open-eq-07-result.srx"),
            ("open-world", open_eq_08, "open-eq-08.rq", "data-2.hdt", "open-eq-08-result.srx"),
            ("open-world", open_eq_09, "open-eq-09.rq", "data-2.hdt", "open-eq-09-result.srx"),
            ("open-world", open_eq_10, "open-eq-10.rq", "data-2.hdt", "open-eq-10-result.srx"),
            ("open-world", open_eq_11, "open-eq-11.rq", "data-2.hdt", "open-eq-11-result.srx"),
            ("open-world", open_eq_12, "open-eq-12.rq", "data-2.hdt", "open-eq-12-result.srx"),

            ("open-world", date_1, "date-1.rq", "data-3.hdt", "date-1-result.srx"),
            ("open-world", date_3, "date-3.rq", "data-3.hdt", "date-3-result.srx"),
            ("open-world", date_4, "date-4.rq", "data-3.hdt", "date-4-result.srx"),

            ("open-world", open_cmp_01, "open-cmp-01.rq", "data-4.hdt", "open-cmp-01-result.srx"),
            ("open-world", open_cmp_02, "open-cmp-02.rq", "data-4.hdt", "open-cmp-02-result.srx")
        }
    }

    mod algebra {
        rdf_sparql10_ignore_test! {
            // TODO - Handle multiple data sources
            // ("algebra", join_combo_2, "join-combo-2.rq",
            // ["join-combo-graph-1.hdt", "join-combo-graph-2.hdt"], "join-combo-2.srx")
            ("algebra", join_combo_2, "join-combo-2.rq", "join-combo-graph-1.hdt", "join-combo-2.srx")
        }

        rdf_sparql10_test! {
            ("algebra", nested_opt_1, "two-nested-opt.rq", "two-nested-opt.hdt", "two-nested-opt.srx"),
            ("algebra", nested_opt_2, "two-nested-opt-alt.rq", "two-nested-opt.hdt", "two-nested-opt-alt.srx"),
            ("algebra", opt_filter_1, "opt-filter-1.rq", "opt-filter-1.hdt", "opt-filter-1.srx"),
            ("algebra", opt_filter_2, "opt-filter-2.rq", "opt-filter-2.hdt", "opt-filter-2.srx"),
            ("algebra", opt_filter_3, "opt-filter-3.rq", "opt-filter-3.hdt", "opt-filter-3.srx"),
            ("algebra", filter_place_1, "filter-placement-1.rq", "data-2.hdt", "filter-placement-1.srx"),
            ("algebra", filter_place_2, "filter-placement-2.rq", "data-2.hdt", "filter-placement-2.srx"),
            ("algebra", filter_place_3, "filter-placement-3.rq", "data-2.hdt", "filter-placement-3.srx"),
            ("algebra", filter_nested_1, "filter-nested-1.rq", "data-1.hdt", "filter-nested-1.srx"),
            ("algebra", filter_nested_2, "filter-nested-2.rq", "data-1.hdt", "filter-nested-2.srx"),
            ("algebra", filter_scope_1, "filter-scope-1.rq", "data-2.hdt", "filter-scope-1.srx"),
            ("algebra", join_scope_1, "var-scope-join-1.rq", "var-scope-join-1.hdt", "var-scope-join-1.srx"),
            ("algebra", join_combo_1, "join-combo-1.rq", "join-combo-graph-2.hdt", "join-combo-1.srx")
        }
    }

    mod bnode_coreference {
        rdf_sparql10_test! {
            ("bnode-coreference", dawg_bnode_coref_001, "query.rq", "data.hdt", "result.ttl")
        }
    }

    mod optional {
        rdf_sparql10_ignore_test! {
            // TODO - Handle multiple data sources
            ("optional", dawg_optional_complex_2,
             "q-opt-complex-2.rq", "complex-data-1.hdt", "result-opt-complex-2.ttl"),
            // TODO - Handle multiple data sources
            ("optional", dawg_optional_complex_3,
             "q-opt-complex-3.rq", "complex-data-1.hdt"," result-opt-complex-3.ttl"),
            // TODO - Handle multiple data sources
            ("optional", dawg_optional_complex_4,
             "q-opt-complex-4.rq", "complex-data-1.hdt"," result-opt-complex-4.ttl")
        }

        rdf_sparql10_test! {
            ("optional", dawg_optional_complex_1,
             "q-opt-complex-1.rq", "complex-data-1.hdt", "result-opt-complex-1.ttl"),
            ("optional", dawg_optional_001,
             "q-opt-1.rq", "data.hdt", "result-opt-1.ttl"),
            ("optional", dawg_optional_002,
             "q-opt-2.rq", "data.hdt", "result-opt-2.ttl"),
            ("optional", dawg_union_001,
             "q-opt-3.rq", "data.hdt", "result-opt-3.ttl")
        }
    }

    mod graph {
        // TODO - HDT does not support named graphs. See
        // https://doi.org/10.1007/978-3-319-93417-4_13 for possible
        // opportunities to add support for named graphs.
        rdf_sparql10_ignore_test! {
            // Uses qt:graphData
            ("graph", dawg_graph_02, "graph-02.rq", "data-g1.hdt", "graph-02.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_03, "graph-03.rq", "data-g1.hdt", "graph-03.ttl"),
            // GRAPH sytanx in SPARQL
            ("graph", dawg_graph_04, "graph-04.rq", "data-g1.hdt", "graph-04.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_05, "graph-05.rq", "data-g1.hdt", "graph-05.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_06, "graph-06.rq", "data-g1.hdt", "graph-06.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_07, "graph-07.rq", "data-g1.hdt", "graph-07.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_08, "graph-08.rq", "data-g1.hdt", "graph-08.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_09, "graph-09.rq", "data-g3.hdt", "graph-09.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_10b, "graph-10.rq", "data-g3.hdt", "graph-10.ttl"),
            // Uses qt:graphData
            ("graph", dawg_graph_11, "graph-11.rq", "data-g1.hdt", "graph-11.ttl")
        }

        rdf_sparql10_test! {
            ("graph", dawg_graph_01, "graph-01.rq", "data-g1.hdt", "graph-01.ttl")
        }
    }

    mod dataset {
        // TODO These could be run as-is as regression tests.

        // TODO These could be modified so that the FROM clause specifies an HDT file as source.
    }

    mod type_promotion {
        rdf_sparql10_test! {
            ("type-promotion", type_promotion_01, "tP-double-double.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_02, "tP-double-float.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_03, "tP-double-decimal.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_04, "tP-float-float.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_05, "tP-float-decimal.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_06, "tP-decimal-decimal.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_07, "tP-integer-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_08, "tP-nonPositiveInteger-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_09, "tP-negativeInteger-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_10, "tP-long-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_11, "tP-int-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_12, "tP-short-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_13, "tP-byte-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_14, "tP-nonNegativeInteger-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_15, "tP-unsignedLong-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_16, "tP-unsignedInt-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_17, "tP-unsignedShort-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_18, "tP-unsignedByte-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_19, "tP-positiveInteger-short.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_20, "tP-short-double.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_21, "tP-short-float.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_22, "tP-short-decimal.rq", "tP.hdt", "true.ttl"),
            ("type-promotion", type_promotion_23, "tP-short-short-fail.rq", "tP.hdt", "false.ttl"),
            ("type-promotion", type_promotion_24, "tP-byte-short-fail.rq", "tP.hdt", "false.ttl"),
            ("type-promotion", type_promotion_25, "tP-short-long-fail.rq", "tP.hdt", "false.ttl"),
            ("type-promotion", type_promotion_26, "tP-short-int-fail.rq", "tP.hdt", "false.ttl"),
            ("type-promotion", type_promotion_27, "tP-short-byte-fail.rq", "tP.hdt", "false.ttl"),
            ("type-promotion", type_promotion_28, "tP-double-float-fail.rq", "tP.hdt", "false.ttl"),
            ("type-promotion", type_promotion_29, "tP-double-decimal-fail.rq", "tP.hdt", "false.ttl"),
            ("type-promotion", type_promotion_30, "tP-float-decimal-fail.rq", "tP.hdt", "false.ttl")
        }
    }

    mod cast {
        rdf_sparql10_test! {
            ("cast", cast_bool, "cast-bool.rq", "data.hdt", "cast-bool.srx"),
            ("cast", cast_dt, "cast-dT.rq", "data.hdt", "cast-dT.srx"),
            ("cast", cast_dbl, "cast-dbl.rq", "data.hdt", "cast-dbl.srx"),
            ("cast", cast_dec, "cast-dec.rq", "data.hdt", "cast-dec.srx"),
            ("cast", cast_flt, "cast-flt.rq", "data.hdt", "cast-flt.srx"),
            ("cast", cast_int, "cast-int.rq", "data.hdt", "cast-int.srx"),
            ("cast", cast_str, "cast-str.rq", "data.hdt", "cast-str.srx")
        }
    }

    mod boolean_effective_value {
        rdf_sparql10_test! {
            ("boolean-effective-value", dawg_bev_1, "query-bev-1.rq", "data-1.hdt", "result-bev-1.ttl"),
            ("boolean-effective-value", dawg_bev_2, "query-bev-2.rq", "data-1.hdt", "result-bev-2.ttl"),
            ("boolean-effective-value", dawg_bev_3, "query-bev-3.rq", "data-1.hdt", "result-bev-3.ttl"),
            ("boolean-effective-value", dawg_bev_4, "query-bev-4.rq", "data-1.hdt", "result-bev-4.ttl"),
            ("boolean-effective-value", dawg_bev_5, "query-bev-5.rq", "data-2.hdt", "result-bev-5.ttl"),
            ("boolean-effective-value", dawg_bev_6, "query-bev-6.rq", "data-2.hdt", "result-bev-6.ttl"),
            ("boolean-effective-value", dawg_boolean_literal, "query-boolean-literal.rq", "data-1.hdt", "result-boolean-literal.ttl")
        }
    }

    mod bound {
        rdf_sparql10_test! {
            ("bound", dawg_bound_query_001, "bound1.rq", "data.hdt", "bound1-result.ttl")
        }
    }

    mod expr_builtin {
        rdf_sparql10_ignore_test! {
            // Multiple writing of the same xsd:integer. Our system does strong normalization.
            ("expr-builtin", dawg_str_1, "q-str-1.rq", "data-builtin-1.hdt", "result-str-1.ttl"),
            ("expr-builtin", dawg_str_2, "q-str-2.rq", "data-builtin-1.hdt", "result-str-2.ttl"),

            // Multiple writing of the same xsd:double. Our system does strong normalization.
            ("expr-builtin", same_term_simple, "sameTerm.rq", "data-builtin-1.hdt", "result-sameTerm.ttl"),
            ("expr-builtin", same_term_eq, "sameTerm-eq.rq", "data-builtin-1.hdt", "result-sameTerm-eq.ttl"),
            ("expr-builtin", same_term_not_eq, "sameTerm-not-eq.rq", "data-builtin-1.hdt", "result-sameTerm-not-eq.ttl")
        }

        rdf_sparql10_test! {
            ("expr-builtin", dawg_datatype_1, "q-datatype-1.rq", "data-builtin-1.hdt", "result-datatype-1.ttl"),
            ("expr-builtin", dawg_datatype_2, "q-datatype-2.rq", "data-builtin-2.hdt", "result-datatype-2.srx"),
            ("expr-builtin", dawg_datatype_3, "q-datatype-3.rq", "data-builtin-2.hdt", "result-datatype-3.srx"),
            ("expr-builtin", dawg_isblank_1, "q-blank-1.rq", "data-builtin-1.hdt", "result-blank-1.ttl"),
            ("expr-builtin", dawg_isiri_1, "q-iri-1.rq", "data-builtin-1.hdt", "result-iri-1.ttl"),
            ("expr-builtin", dawg_isliteral_1, "q-isliteral-1.rq", "data-builtin-2.hdt", "result-isliteral-1.ttl"),
            ("expr-builtin", dawg_isuri_1, "q-uri-1.rq", "data-builtin-1.hdt", "result-uri-1.ttl"),
            ("expr-builtin", dawg_lang_1, "q-lang-1.rq", "data-builtin-2.hdt", "result-lang-1.srx"),
            ("expr-builtin", dawg_lang_2, "q-lang-2.rq", "data-builtin-2.hdt", "result-lang-2.srx"),
            ("expr-builtin", dawg_lang_3, "q-lang-3.rq", "data-builtin-2.hdt", "result-lang-3.srx"),
            ("expr-builtin", dawg_langmatches_1, "q-langMatches-1.rq", "data-langMatches.hdt", "result-langMatches-1.ttl"),
            ("expr-builtin", dawg_langmatches_2, "q-langMatches-2.rq", "data-langMatches.hdt", "result-langMatches-2.ttl"),
            ("expr-builtin", dawg_langmatches_3, "q-langMatches-3.rq", "data-langMatches.hdt", "result-langMatches-3.ttl"),
            ("expr-builtin", dawg_langmatches_4, "q-langMatches-4.rq", "data-langMatches.hdt", "result-langMatches-4.ttl"),
            ("expr-builtin", dawg_langmatches_basic, "q-langMatches-de-de.rq", "data-langMatches-de.hdt", "result-langMatches-de.ttl"),
            ("expr-builtin", dawg_str_3, "q-str-3.rq", "data-builtin-1.hdt", "result-str-3.ttl"),
            ("expr-builtin", dawg_str_4, "q-str-4.rq", "data-builtin-1.hdt", "result-str-4.ttl"),
            ("expr-builtin", lang_case_insensitive_eq, "lang-case-sensitivity-eq.rq", "lang-case-sensitivity.hdt", "lang-case-insensitive-eq.srx"),
            ("expr-builtin", lang_case_insensitive_ne, "lang-case-sensitivity-ne.rq", "lang-case-sensitivity.hdt", "lang-case-insensitive-ne.srx")
        }
    }

    mod expr_ops {
        rdf_sparql10_test! {
            ("expr-ops", ge_1, "query-ge-1.rq", "data.hdt", "result-ge-1.srx"),
            ("expr-ops", le_1, "query-le-1.rq", "data.hdt", "result-le-1.srx"),
            ("expr-ops", minus_1, "query-minus-1.rq", "data.hdt", "result-minus-1.srx"),
            ("expr-ops", mul_1, "query-mul-1.rq", "data.hdt", "result-mul-1.srx"),
            ("expr-ops", plus_1, "query-plus-1.rq", "data.hdt", "result-plus-1.srx"),
            ("expr-ops", unminus_1, "query-unminus-1.rq", "data.hdt", "result-unminus-1.srx"),
            ("expr-ops", unplus_1, "query-unplus-1.rq", "data.hdt", "result-unplus-1.srx")
        }
    }

    mod expr_equals {
        rdf_sparql10_ignore_test! {
            // Multiple writing of the same xsd:integer. Our system does strong normalization.
            ("expr-equals", eq_graph_1, "query-eq-graph-1.rq", "data-eq.hdt", "result-eq-graph-1.ttl"),
            ("expr-equals", eq_graph_2, "query-eq-graph-2.rq", "data-eq.hdt", "result-eq-graph-2.ttl")
        }

        rdf_sparql10_test! {
            ("expr-equals", eq_1, "query-eq-1.rq", "data-eq.hdt", "result-eq-1.ttl"),
            ("expr-equals", eq_2, "query-eq-2.rq", "data-eq.hdt", "result-eq-2.ttl"),
            ("expr-equals", eq_2_1, "query-eq2-1.rq", "data-eq.hdt", "result-eq2-1.ttl"),
            ("expr-equals", eq_2_2, "query-eq2-1.rq", "data-eq.hdt", "result-eq2-1.ttl"),
            ("expr-equals", eq_3, "query-eq-3.rq", "data-eq.hdt", "result-eq-3.ttl"),
            ("expr-equals", eq_4, "query-eq-4.rq", "data-eq.hdt", "result-eq-4.ttl"),
            ("expr-equals", eq_5, "query-eq-5.rq", "data-eq.hdt", "result-eq-5.ttl"),
            ("expr-equals", eq_graph_3, "query-eq-graph-3.rq", "data-eq.hdt", "result-eq-graph-3.ttl"),
            ("expr-equals", eq_graph_4, "query-eq-graph-4.rq", "data-eq.hdt", "result-eq-graph-4.ttl"),
            ("expr-equals", eq_graph_5, "query-eq-graph-5.rq", "data-eq.hdt", "result-eq-graph-5.ttl")
        }
    }

    mod regex {
        rdf_sparql10_test! {
            ("regex", dawg_regex_001, "regex-query-001.rq", "regex-data-01.hdt", "regex-result-001.ttl"),
            ("regex", dawg_regex_002, "regex-query-002.rq", "regex-data-01.hdt", "regex-result-002.ttl"),
            ("regex", dawg_regex_003, "regex-query-003.rq", "regex-data-01.hdt", "regex-result-003.ttl"),
            ("regex", dawg_regex_004, "regex-query-004.rq", "regex-data-01.hdt", "regex-result-004.ttl")
        }
    }

    mod i18n {
        rdf_sparql10_test! {
            ("i18n", kanji_1, "kanji-01.rq", "kanji.hdt", "kanji-01-results.ttl"),
            ("i18n", kanji_2, "kanji-02.rq", "kanji.hdt", "kanji-02-results.ttl"),
            ("i18n", normalization_1, "normalization-01.rq", "normalization-01.hdt", "normalization-01-results.ttl"),

            // It looks like hdt-java drops the "." and ".." from the URL on creation of the HDT.
            //
            // HDT Content
            //
            // $ hdtSearch normalization-02.hdt
            // >> ? ? ?
            // http://example/vocab#s1 http://example/vocab#p example://a/b/c/%7Bfoo%7D#xyz
            // http://example/vocab#s2 http://example/vocab#p eXAMPLE://a/b/%63/%7bfoo%7d#xyz
            //
            // However, hdt-cpp preserves it. Therefore, hdt-cpp is used to generate the test data.
            // See https://github.com/rdfhdt/hdt-java/issues/203
            ("i18n", normalization_2, "normalization-02.rq", "normalization-02.hdt", "normalization-02-results.ttl"),

            ("i18n", normalization_3, "normalization-03.rq", "normalization-03.hdt", "normalization-03-results.ttl")
        }
    }

    mod construct {
        rdf_sparql10_test! {
            ("construct", construct_1, "query-ident.rq", "data-ident.hdt", "result-ident.ttl"),
            ("construct", construct_2, "query-subgraph.rq", "data-ident.hdt", "result-subgraph.ttl"),
            ("construct", construct_3, "query-reif-1.rq", "data-reif.hdt", "result-reif.ttl"),
            ("construct", construct_4, "query-reif-2.rq", "data-reif.hdt", "result-reif.ttl"),
            ("construct", construct_5, "query-construct-optional.rq", "data-opt.hdt", "result-construct-optional.ttl")
        }
    }

    mod ask {
        rdf_sparql10_test! {
            ("ask", ask_1, "ask-1.rq", "data.hdt", "ask-1.srx"),
            ("ask", ask_4, "ask-4.rq", "data.hdt", "ask-4.srx"),
            ("ask", ask_7, "ask-7.rq", "data.hdt", "ask-7.srx"),
            ("ask", ask_8, "ask-8.rq", "data.hdt", "ask-8.srx")
        }
    }

    mod distinct {
        rdf_sparql10_ignore_test! {
            // Multiple writing of the same xsd:integer. Our system does strong normalization.
            ("distinct", distinct_1, "distinct-1.rq", "data-num.hdt", "distinct-num.srx"),
            ("distinct", distinct_9, "distinct-1.rq", "data-all.hdt", "distinct-all.srx")
        }

        rdf_sparql10_test! {
            ("distinct", distinct_2, "distinct-1.rq", "data-str.hdt", "distinct-str.srx"),
            ("distinct", distinct_3, "distinct-1.rq", "data-node.hdt", "distinct-node.srx"),
            ("distinct", distinct_4, "distinct-2.rq", "data-opt.hdt", "distinct-opt.srx"),
            ("distinct", distinct_star_1, "distinct-star-1.rq", "data-star.hdt", "distinct-star-1.srx"),
            ("distinct", no_distinct_1, "no-distinct-1.rq", "data-num.hdt", "no-distinct-num.srx"),
            ("distinct", no_distinct_2, "no-distinct-1.rq", "data-str.hdt", "no-distinct-str.srx"),
            ("distinct", no_distinct_3, "no-distinct-1.rq", "data-node.hdt", "no-distinct-node.srx"),
            ("distinct", no_distinct_4, "no-distinct-2.rq", "data-opt.hdt", "no-distinct-opt.srx"),
            ("distinct", no_distinct_9, "no-distinct-1.rq", "data-all.hdt", "no-distinct-all.srx")
        }
    }

    mod sort {
        rdf_sparql10_test! {
            ("sort", dawg_sort_1, "query-sort-1.rq", "data-sort-1.hdt", "result-sort-1.rdf"),
            ("sort", dawg_sort_10, "query-sort-10.rq", "data-sort-9.hdt", "result-sort-10.rdf"),
            ("sort", dawg_sort_2, "query-sort-2.rq", "data-sort-1.hdt", "result-sort-2.rdf"),
            ("sort", dawg_sort_3, "query-sort-3.rq", "data-sort-3.hdt", "result-sort-3.rdf"),
            ("sort", dawg_sort_4, "query-sort-4.rq", "data-sort-4.hdt", "result-sort-4.rdf"),
            ("sort", dawg_sort_5, "query-sort-5.rq", "data-sort-4.hdt", "result-sort-5.rdf"),
            ("sort", dawg_sort_6, "query-sort-6.rq", "data-sort-6.hdt", "result-sort-6.rdf"),
            ("sort", dawg_sort_7, "query-sort-4.rq", "data-sort-7.hdt", "result-sort-7.rdf"),
            ("sort", dawg_sort_8, "query-sort-4.rq", "data-sort-8.hdt", "result-sort-8.rdf"),
            ("sort", dawg_sort_9, "query-sort-9.rq", "data-sort-9.hdt", "result-sort-9.rdf"),
            ("sort", dawg_sort_builtin, "query-sort-builtin.rq", "data-sort-builtin.hdt", "result-sort-builtin.ttl"),
            ("sort", dawg_sort_function, "query-sort-function.rq", "data-sort-function.hdt", "result-sort-function.ttl"),
            ("sort", dawg_sort_numbers, "query-sort-numbers.rq", "data-sort-numbers.hdt", "result-sort-numbers.ttl")
        }
    }

    mod solution_seq {
        rdf_sparql10_test! {
            ("solution-seq", limit_1, "slice-01.rq", "data.hdt", "slice-results-01.ttl"),
            ("solution-seq", limit_2, "slice-02.rq", "data.hdt", "slice-results-02.ttl"),
            ("solution-seq", limit_3, "slice-03.rq", "data.hdt", "slice-results-03.ttl"),
            ("solution-seq", limit_4, "slice-04.rq", "data.hdt", "slice-results-04.ttl"),
            ("solution-seq", offset_1, "slice-10.rq", "data.hdt", "slice-results-10.ttl"),
            ("solution-seq", offset_2, "slice-11.rq", "data.hdt", "slice-results-11.ttl"),
            ("solution-seq", offset_3, "slice-12.rq", "data.hdt", "slice-results-12.ttl"),
            ("solution-seq", offset_4, "slice-13.rq", "data.hdt", "slice-results-13.ttl"),
            ("solution-seq", slice_1, "slice-20.rq", "data.hdt", "slice-results-20.ttl"),
            ("solution-seq", slice_2, "slice-21.rq", "data.hdt", "slice-results-21.ttl"),
            ("solution-seq", slice_3, "slice-22.rq", "data.hdt", "slice-results-22.ttl"),
            ("solution-seq", slice_4, "slice-23.rq", "data.hdt", "slice-results-23.ttl"),
            ("solution-seq", slice_5, "slice-24.rq", "data.hdt", "slice-results-24.ttl")
        }
    }

    mod reduced {
        rdf_sparql10_ignore_test! {
            // This test relies on naive iteration on the input file
            ("reduced", reduced_2, "reduced-2.rq", "reduced-str.hdt", "reduced-2.srx")
        }

        // Original Data
        // <http://example/x1> <http://example/p> "abc" .
        // <http://example/x1> <http://example/q> "abc" .
        // <http://example/x2> <http://example/p> "abc" .
        //
        // HDT
        // <http://example/x1> <http://example/p> "abc" .
        // <http://example/x1> <http://example/q> "abc" .
        // <http://example/x2> <http://example/p> "abc" .
        //
        // Query
        // SELECT REDUCED *
        // WHERE {
        //   { ?s :p ?o } UNION { ?s :q ?o }
        // }
        //
        // Expected
        // s o
        // <http://example/x1> "abc"
        // <http://example/x1> "abc"
        // <http://example/x2> "abc"
        //
        // Actual
        // s o
        // <http://example/x1> "abc"
        // <http://example/x2> "abc"
        //
        // The actual is passable per
        // https://www.w3.org/TR/sparql11-query/#modDuplicates
        rdf_sparql10_customized_test! {
            ("reduced", reduced_1, "reduced-1.rq", "reduced-star.hdt", "reduced-1.srx")
        }
    }
}
