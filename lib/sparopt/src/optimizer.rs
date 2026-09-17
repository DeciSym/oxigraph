use crate::algebra::{
    Expression, GraphPattern, JoinAlgorithm, LeftJoinAlgorithm, MinusAlgorithm, OrderExpression,
};
use crate::type_inference::{
    VariableType, VariableTypes, infer_expression_type, infer_graph_pattern_types,
};
use oxrdf::vocab::rdf;
use oxrdf::{NamedNodeRef, TermRef, Variable};
use spargebra::algebra::PropertyPathExpression;
use spargebra::term::{GroundTermPattern, NamedNodePattern};
use std::cmp::{max, min};

/// Supplies the optimizer with the real number of quads matching a pattern.
///
/// Join reordering is only as good as its size estimates, and without help the optimizer has
/// nothing to go on but the *shape* of a pattern -- which position is a constant and which is a
/// variable. That cannot tell a predicate occurring three times from one occurring three million
/// times, so two same-shaped patterns tie and the order the query happened to be written in
/// decides the plan.
///
/// A store that can count matching quads cheaply -- an HDT package, say, whose index knows the
/// extent of every pattern -- implements this and gets its real numbers used instead.
///
/// Only the *constant* positions of a pattern are passed: a variable is `None` even when the
/// optimizer knows the input will bind it, because at planning time the value it will be bound to
/// is not yet known. The optimizer scales the returned count to account for those.
///
/// Implementations should be cheap. This is called once per pattern per reordering decision, so an
/// implementation that has to scan to answer should return `None` instead.
pub trait CardinalityEstimator {
    /// The number of quads matching a pattern whose constant positions are the given terms, or
    /// `None` when the estimator cannot answer cheaply.
    fn quad_pattern_size(
        &self,
        subject: Option<TermRef<'_>>,
        predicate: Option<NamedNodeRef<'_>>,
        object: Option<TermRef<'_>>,
        graph_name: Option<Option<NamedNodeRef<'_>>>,
    ) -> Option<usize>;
}

/// The estimator used when the caller supplies none: never answers, so the shape-based estimates
/// are used unchanged.
pub struct NoCardinalityEstimator;

impl CardinalityEstimator for NoCardinalityEstimator {
    fn quad_pattern_size(
        &self,
        _subject: Option<TermRef<'_>>,
        _predicate: Option<NamedNodeRef<'_>>,
        _object: Option<TermRef<'_>>,
        _graph_name: Option<Option<NamedNodeRef<'_>>>,
    ) -> Option<usize> {
        None
    }
}

pub struct Optimizer;

impl Optimizer {
    pub fn optimize_graph_pattern(pattern: GraphPattern) -> GraphPattern {
        Self::optimize_graph_pattern_with_cardinality(pattern, &NoCardinalityEstimator)
    }

    /// Optimize a pattern, asking `cardinality` for the real size of each quad pattern.
    pub fn optimize_graph_pattern_with_cardinality(
        pattern: GraphPattern,
        cardinality: &dyn CardinalityEstimator,
    ) -> GraphPattern {
        let pattern = Self::normalize_pattern(pattern, &VariableTypes::default());
        let pattern = Self::reorder_joins(pattern, &VariableTypes::default(), cardinality);
        Self::push_filters(pattern, Vec::new(), &VariableTypes::default())
    }

    /// Normalize the pattern, discarding any join ordering information
    fn normalize_pattern(pattern: GraphPattern, input_types: &VariableTypes) -> GraphPattern {
        match pattern {
            GraphPattern::QuadPattern {
                subject,
                predicate,
                object,
                graph_name,
            } => GraphPattern::QuadPattern {
                subject,
                predicate,
                object,
                graph_name,
            },
            GraphPattern::Path {
                subject,
                path,
                object,
                graph_name,
            } => GraphPattern::Path {
                subject,
                path,
                object,
                graph_name,
            },
            GraphPattern::Graph { graph_name } => GraphPattern::Graph { graph_name },
            GraphPattern::Join {
                left,
                right,
                algorithm,
            } => GraphPattern::join(
                Self::normalize_pattern(*left, input_types),
                Self::normalize_pattern(*right, input_types),
                algorithm,
            ),
            GraphPattern::LeftJoin {
                left,
                right,
                expression,
                algorithm,
            } => {
                let left = Self::normalize_pattern(*left, input_types);
                let right = Self::normalize_pattern(*right, input_types);
                let mut inner_types = infer_graph_pattern_types(&left, input_types.clone());
                inner_types.intersect_with(infer_graph_pattern_types(&right, input_types.clone()));
                GraphPattern::left_join(
                    left,
                    right,
                    Self::normalize_expression(expression, &inner_types),
                    algorithm,
                )
            }
            #[cfg(feature = "sep-0006")]
            GraphPattern::Lateral { left, right } => {
                let left = Self::normalize_pattern(*left, input_types);
                let left_types = infer_graph_pattern_types(&left, input_types.clone());
                let right = Self::normalize_pattern(*right, &left_types);
                GraphPattern::lateral(left, right)
            }
            GraphPattern::Filter { inner, expression } => {
                let inner = Self::normalize_pattern(*inner, input_types);
                let inner_types = infer_graph_pattern_types(&inner, input_types.clone());
                let expression = Self::normalize_expression(expression, &inner_types);
                let expression_type = infer_expression_type(&expression, &inner_types);
                if expression_type == VariableType::UNDEF {
                    GraphPattern::empty()
                } else {
                    GraphPattern::filter(inner, expression)
                }
            }
            GraphPattern::Union { inner } => GraphPattern::union_all(
                inner
                    .into_iter()
                    .map(|e| Self::normalize_pattern(e, input_types)),
            ),
            GraphPattern::Extend {
                inner,
                variable,
                expression,
            } => {
                let inner = Self::normalize_pattern(*inner, input_types);
                let inner_types = infer_graph_pattern_types(&inner, input_types.clone());
                let expression = Self::normalize_expression(expression, &inner_types);
                let expression_type = infer_expression_type(&expression, &inner_types);
                if expression_type == VariableType::UNDEF {
                    // TODO: valid?
                    inner
                } else {
                    GraphPattern::extend(inner, variable, expression)
                }
            }
            GraphPattern::Minus {
                left,
                right,
                algorithm,
            } => GraphPattern::minus(
                Self::normalize_pattern(*left, input_types),
                Self::normalize_pattern(*right, input_types),
                algorithm,
            ),
            GraphPattern::Values {
                variables,
                bindings,
            } => GraphPattern::values(variables, bindings),
            GraphPattern::OrderBy { inner, expression } => {
                let inner = Self::normalize_pattern(*inner, input_types);
                let inner_types = infer_graph_pattern_types(&inner, input_types.clone());
                GraphPattern::order_by(
                    inner,
                    expression
                        .into_iter()
                        .map(|e| match e {
                            OrderExpression::Asc(e) => {
                                OrderExpression::Asc(Self::normalize_expression(e, &inner_types))
                            }
                            OrderExpression::Desc(e) => {
                                OrderExpression::Desc(Self::normalize_expression(e, &inner_types))
                            }
                        })
                        .collect(),
                )
            }
            GraphPattern::Project { inner, variables } => {
                GraphPattern::project(Self::normalize_pattern(*inner, input_types), variables)
            }
            GraphPattern::Distinct { inner } => {
                GraphPattern::distinct(Self::normalize_pattern(*inner, input_types))
            }
            GraphPattern::Reduced { inner } => {
                GraphPattern::reduced(Self::normalize_pattern(*inner, input_types))
            }
            GraphPattern::Slice {
                inner,
                start,
                length,
            } => GraphPattern::slice(Self::normalize_pattern(*inner, input_types), start, length),
            GraphPattern::Group {
                inner,
                variables,
                aggregates,
            } => {
                // TODO: min, max and sample don't care about DISTINCT
                GraphPattern::group(
                    Self::normalize_pattern(*inner, input_types),
                    variables,
                    aggregates,
                )
            }
            GraphPattern::Service { .. } => {
                // We leave this problem to the remote SPARQL endpoint
                pattern
            }
        }
    }

    fn normalize_expression(expression: Expression, types: &VariableTypes) -> Expression {
        match expression {
            Expression::NamedNode(node) => node.into(),
            Expression::Literal(literal) => literal.into(),
            Expression::Variable(variable) => variable.into(),
            Expression::Or(inner) => Expression::or_all(
                inner
                    .into_iter()
                    .map(|e| Self::normalize_expression(e, types)),
            ),
            Expression::And(inner) => Expression::and_all(
                inner
                    .into_iter()
                    .map(|e| Self::normalize_expression(e, types)),
            ),
            Expression::Equal(left, right) => {
                let left = Self::normalize_expression(*left, types);
                let left_types = infer_expression_type(&left, types);
                let right = Self::normalize_expression(*right, types);
                let right_types = infer_expression_type(&right, types);
                #[allow(unused_mut, clippy::allow_attributes)]
                let mut must_use_equal = left_types.literal && right_types.literal;
                #[cfg(feature = "sparql-12")]
                {
                    must_use_equal = must_use_equal || left_types.triple && right_types.triple;
                }
                if must_use_equal {
                    Expression::equal(left, right)
                } else {
                    Expression::same_term(left, right)
                }
            }
            Expression::SameTerm(left, right) => Expression::same_term(
                Self::normalize_expression(*left, types),
                Self::normalize_expression(*right, types),
            ),
            Expression::Greater(left, right) => Expression::greater(
                Self::normalize_expression(*left, types),
                Self::normalize_expression(*right, types),
            ),
            Expression::GreaterOrEqual(left, right) => Expression::greater_or_equal(
                Self::normalize_expression(*left, types),
                Self::normalize_expression(*right, types),
            ),
            Expression::Less(left, right) => Expression::less(
                Self::normalize_expression(*left, types),
                Self::normalize_expression(*right, types),
            ),
            Expression::LessOrEqual(left, right) => Expression::less_or_equal(
                Self::normalize_expression(*left, types),
                Self::normalize_expression(*right, types),
            ),
            Expression::Add(left, right) => {
                Self::normalize_expression(*left, types) + Self::normalize_expression(*right, types)
            }
            Expression::Subtract(left, right) => {
                Self::normalize_expression(*left, types) - Self::normalize_expression(*right, types)
            }
            Expression::Multiply(left, right) => {
                Self::normalize_expression(*left, types) * Self::normalize_expression(*right, types)
            }
            Expression::Divide(left, right) => {
                Self::normalize_expression(*left, types) / Self::normalize_expression(*right, types)
            }
            Expression::UnaryPlus(inner) => {
                Expression::unary_plus(Self::normalize_expression(*inner, types))
            }
            Expression::UnaryMinus(inner) => -Self::normalize_expression(*inner, types),
            Expression::Not(inner) => !Self::normalize_expression(*inner, types),
            Expression::Exists(inner) => Expression::exists(Self::normalize_pattern(*inner, types)),
            Expression::Bound(variable) => {
                let t = types.get(&variable);
                if !t.undef {
                    true.into()
                } else if t == VariableType::UNDEF {
                    false.into()
                } else {
                    Expression::Bound(variable)
                }
            }
            Expression::If(cond, then, els) => Expression::if_cond(
                Self::normalize_expression(*cond, types),
                Self::normalize_expression(*then, types),
                Self::normalize_expression(*els, types),
            ),
            Expression::Coalesce(inners) => Expression::coalesce(
                inners
                    .into_iter()
                    .map(|e| Self::normalize_expression(e, types))
                    .collect(),
            ),
            Expression::FunctionCall(name, args) => Expression::call(
                name,
                args.into_iter()
                    .map(|e| Self::normalize_expression(e, types))
                    .collect(),
            ),
        }
    }

    fn push_filters(
        pattern: GraphPattern,
        mut filters: Vec<Expression>,
        input_types: &VariableTypes,
    ) -> GraphPattern {
        match pattern {
            GraphPattern::QuadPattern { .. }
            | GraphPattern::Path { .. }
            | GraphPattern::Graph { .. }
            | GraphPattern::Values { .. } => {
                GraphPattern::filter(pattern, Expression::and_all(filters))
            }
            GraphPattern::Join {
                left,
                right,
                algorithm,
            } => {
                let left_types = infer_graph_pattern_types(&left, input_types.clone());
                let right_types = infer_graph_pattern_types(&right, input_types.clone());
                let mut left_filters = Vec::new();
                let mut right_filters = Vec::new();
                let mut final_filters = Vec::new();
                for filter in filters {
                    let push_left = are_all_expression_variables_bound(&filter, &left_types);
                    let push_right = are_all_expression_variables_bound(&filter, &right_types);
                    if push_left {
                        if push_right {
                            left_filters.push(filter.clone());
                            right_filters.push(filter);
                        } else {
                            left_filters.push(filter);
                        }
                    } else if push_right {
                        right_filters.push(filter);
                    } else {
                        final_filters.push(filter);
                    }
                }
                GraphPattern::filter(
                    GraphPattern::join(
                        Self::push_filters(*left, left_filters, input_types),
                        Self::push_filters(*right, right_filters, input_types),
                        algorithm,
                    ),
                    Expression::and_all(final_filters),
                )
            }
            #[cfg(feature = "sep-0006")]
            GraphPattern::Lateral { left, right } => {
                let left_types = infer_graph_pattern_types(&left, input_types.clone());
                let mut left_filters = Vec::new();
                let mut right_filters = Vec::new();
                for filter in filters {
                    let push_left = are_all_expression_variables_bound(&filter, &left_types);
                    if push_left {
                        left_filters.push(filter);
                    } else {
                        right_filters.push(filter);
                    }
                }
                let left = Self::push_filters(*left, left_filters, input_types);
                let right = Self::push_filters(*right, right_filters, &left_types);
                if let GraphPattern::Filter {
                    inner: inner_right,
                    expression,
                } = right
                {
                    // We prefer to have filter out of the lateral rather than inside the right part
                    GraphPattern::filter(GraphPattern::lateral(left, *inner_right), expression)
                } else {
                    GraphPattern::lateral(left, right)
                }
            }
            GraphPattern::LeftJoin {
                left,
                right,
                expression,
                algorithm,
            } => {
                let left_types = infer_graph_pattern_types(&left, input_types.clone());
                let right_types = infer_graph_pattern_types(&right, input_types.clone());
                let mut left_filters = Vec::new();
                let mut right_filters = Vec::new();
                let mut final_filters = Vec::new();
                for filter in filters {
                    let push_left = are_all_expression_variables_bound(&filter, &left_types);
                    if push_left {
                        left_filters.push(filter);
                    } else {
                        final_filters.push(filter);
                    }
                }
                let expression = if expression.effective_boolean_value().is_none()
                    && (are_all_expression_variables_bound(&expression, &right_types)
                        || are_no_expression_variables_bound(&expression, &left_types))
                {
                    right_filters.push(expression);
                    true.into()
                } else {
                    expression
                };
                GraphPattern::filter(
                    GraphPattern::left_join(
                        Self::push_filters(*left, left_filters, input_types),
                        Self::push_filters(*right, right_filters, input_types),
                        expression,
                        algorithm,
                    ),
                    Expression::and_all(final_filters),
                )
            }
            GraphPattern::Minus {
                left,
                right,
                algorithm,
            } => GraphPattern::minus(
                Self::push_filters(*left, filters, input_types),
                Self::push_filters(*right, Vec::new(), input_types),
                algorithm,
            ),
            GraphPattern::Extend {
                inner,
                expression,
                variable,
            } => {
                // TODO: handle the case where the filter overrides an expression variable (should not happen in SPARQL but allowed in the algebra)
                let mut inner_filters = Vec::new();
                let mut final_filters = Vec::new();
                for filter in filters {
                    let extend_variable_used =
                        filter.used_variables().into_iter().any(|v| *v == variable);
                    if extend_variable_used {
                        final_filters.push(filter);
                    } else {
                        inner_filters.push(filter);
                    }
                }
                GraphPattern::filter(
                    GraphPattern::extend(
                        Self::push_filters(*inner, inner_filters, input_types),
                        variable,
                        expression,
                    ),
                    Expression::and_all(final_filters),
                )
            }
            GraphPattern::Filter { inner, expression } => {
                if let Expression::And(expressions) = expression {
                    filters.extend(expressions)
                } else {
                    filters.push(expression)
                }
                Self::push_filters(*inner, filters, input_types)
            }
            GraphPattern::Union { inner } => GraphPattern::union_all(
                inner
                    .into_iter()
                    .map(|c| Self::push_filters(c, filters.clone(), input_types)),
            ),
            GraphPattern::Slice {
                inner,
                start,
                length,
            } => GraphPattern::filter(
                GraphPattern::slice(
                    Self::push_filters(*inner, Vec::new(), input_types),
                    start,
                    length,
                ),
                Expression::and_all(filters),
            ),
            GraphPattern::Distinct { inner } => {
                GraphPattern::distinct(Self::push_filters(*inner, filters, input_types))
            }
            GraphPattern::Reduced { inner } => {
                GraphPattern::reduced(Self::push_filters(*inner, filters, input_types))
            }
            GraphPattern::Project { inner, variables } => {
                let mut inner_filters = Vec::new();
                let mut final_filters = Vec::new();
                for filter in filters {
                    if filter
                        .used_variables()
                        .into_iter()
                        .all(|variable| variables.contains(variable))
                    {
                        inner_filters.push(filter);
                    } else {
                        // Variables not projected by a subquery are not in scope outside of it.
                        // Pushing such a filter would make the subquery's hidden bindings visible
                        // to the filter, in particular for correlated EXISTS expressions.
                        final_filters.push(filter);
                    }
                }
                GraphPattern::filter(
                    GraphPattern::project(
                        Self::push_filters(*inner, inner_filters, input_types),
                        variables,
                    ),
                    Expression::and_all(final_filters),
                )
            }
            GraphPattern::OrderBy { inner, expression } => {
                GraphPattern::order_by(Self::push_filters(*inner, filters, input_types), expression)
            }
            GraphPattern::Service { .. } => {
                // TODO: we can be smart and push some filters
                // But we need to check the behavior of SILENT that can transform no results into a singleton
                GraphPattern::filter(pattern, Expression::and_all(filters))
            }
            GraphPattern::Group {
                inner,
                variables,
                aggregates,
            } => GraphPattern::filter(
                GraphPattern::group(
                    Self::push_filters(*inner, Vec::new(), input_types),
                    variables,
                    aggregates,
                ),
                Expression::and_all(filters),
            ),
        }
    }

    fn reorder_joins(
        pattern: GraphPattern,
        input_types: &VariableTypes,
        cardinality: &dyn CardinalityEstimator,
    ) -> GraphPattern {
        match pattern {
            GraphPattern::QuadPattern { .. }
            | GraphPattern::Path { .. }
            | GraphPattern::Values { .. }
            | GraphPattern::Graph { .. } => pattern,
            GraphPattern::Join { left, right, .. } => {
                // We flatten the join operation
                let mut to_reorder = Vec::new();
                let mut todo = vec![*right, *left];
                while let Some(e) = todo.pop() {
                    if let GraphPattern::Join { left, right, .. } = e {
                        todo.push(*right);
                        todo.push(*left);
                    } else {
                        to_reorder.push(Self::reorder_joins(e, input_types, cardinality));
                    }
                }

                // We do first type inference
                let to_reorder_types = to_reorder
                    .iter()
                    .map(|p| infer_graph_pattern_types(p, input_types.clone()))
                    .collect::<Vec<_>>();

                // We do greedy join reordering
                let mut output_cartesian_product_joins = Vec::new();
                let mut not_yet_reordered_ids = vec![true; to_reorder.len()];
                // We look for the next connected component to reorder and pick the smallest element
                while let Some(next_entry_id) = not_yet_reordered_ids
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| **v)
                    .map(|(i, _)| i)
                    .min_by_key(|i| {
                        estimate_graph_pattern_size(&to_reorder[*i], input_types, cardinality)
                    })
                {
                    not_yet_reordered_ids[next_entry_id] = false; // It's now done
                    let mut output = to_reorder[next_entry_id].clone();
                    let mut output_types = to_reorder_types[next_entry_id].clone();
                    // We look for an other child to join with that does not blow up the join cost
                    while let Some(next_id) = not_yet_reordered_ids
                        .iter()
                        .enumerate()
                        .filter(|(_, v)| **v)
                        .map(|(i, _)| i)
                        .filter(|i| {
                            has_common_variables(&output_types, &to_reorder_types[*i], input_types)
                        })
                        .min_by_key(|i| {
                            // Estimation of the join cost
                            if cfg!(feature = "sep-0006")
                                && is_fit_for_for_loop_join(
                                    &to_reorder[*i],
                                    input_types,
                                    &output_types,
                                )
                            {
                                estimate_lateral_cost(
                                    &output,
                                    &output_types,
                                    &to_reorder[*i],
                                    input_types,
                                    cardinality,
                                )
                            } else {
                                estimate_join_cost(
                                    &output,
                                    &to_reorder[*i],
                                    &JoinAlgorithm::HashBuildLeftProbeRight {
                                        keys: join_key_variables(
                                            &output_types,
                                            &to_reorder_types[*i],
                                            input_types,
                                        ),
                                    },
                                    input_types,
                                    cardinality,
                                )
                            }
                        })
                    {
                        not_yet_reordered_ids[next_id] = false; // It's now done
                        let next = to_reorder[next_id].clone();
                        #[cfg(feature = "sep-0006")]
                        {
                            output = if is_fit_for_for_loop_join(&next, input_types, &output_types)
                            {
                                GraphPattern::lateral(output, next)
                            } else {
                                GraphPattern::join(
                                    output,
                                    next,
                                    JoinAlgorithm::HashBuildLeftProbeRight {
                                        keys: join_key_variables(
                                            &output_types,
                                            &to_reorder_types[next_id],
                                            input_types,
                                        ),
                                    },
                                )
                            };
                        }
                        #[cfg(not(feature = "sep-0006"))]
                        {
                            output = GraphPattern::join(
                                output,
                                next,
                                JoinAlgorithm::HashBuildLeftProbeRight {
                                    keys: join_key_variables(
                                        &output_types,
                                        &to_reorder_types[next_id],
                                        input_types,
                                    ),
                                },
                            );
                        }
                        output_types.intersect_with(to_reorder_types[next_id].clone());
                    }
                    output_cartesian_product_joins.push(output);
                }
                output_cartesian_product_joins
                    .into_iter()
                    .reduce(|left, right| {
                        let keys = join_key_variables(
                            &infer_graph_pattern_types(&left, input_types.clone()),
                            &infer_graph_pattern_types(&right, input_types.clone()),
                            input_types,
                        );
                        if estimate_graph_pattern_size(&left, input_types, cardinality)
                            <= estimate_graph_pattern_size(&right, input_types, cardinality)
                        {
                            GraphPattern::join(
                                left,
                                right,
                                JoinAlgorithm::HashBuildLeftProbeRight { keys },
                            )
                        } else {
                            GraphPattern::join(
                                right,
                                left,
                                JoinAlgorithm::HashBuildLeftProbeRight { keys },
                            )
                        }
                    })
                    .unwrap()
            }
            #[cfg(feature = "sep-0006")]
            GraphPattern::Lateral { left, right } => {
                let left_types = infer_graph_pattern_types(&left, input_types.clone());
                GraphPattern::lateral(
                    Self::reorder_joins(*left, input_types, cardinality),
                    Self::reorder_joins(*right, &left_types, cardinality),
                )
            }
            GraphPattern::LeftJoin {
                left,
                right,
                expression,
                ..
            } => {
                let left = Self::reorder_joins(*left, input_types, cardinality);
                let left_types = infer_graph_pattern_types(&left, input_types.clone());
                #[cfg(feature = "sep-0006")]
                {
                    let initial_right_types =
                        infer_graph_pattern_types(&right, input_types.clone());
                    if has_common_variables(&left_types, &initial_right_types, input_types) {
                        let lateral_cost =
                            estimate_graph_pattern_size(&left, input_types, cardinality)
                                .saturating_mul(estimate_graph_pattern_size(
                                    &right,
                                    &left_types,
                                    cardinality,
                                ));
                        let keys =
                            join_key_variables(&left_types, &initial_right_types, input_types);
                        let join_cost =
                            estimate_graph_pattern_size(&left, input_types, cardinality)
                                .saturating_mul(estimate_graph_pattern_size(
                                    &right,
                                    input_types,
                                    cardinality,
                                ))
                                .saturating_div(
                                    1_000_usize.saturating_pow(keys.len().try_into().unwrap()),
                                );

                        if lateral_cost <= join_cost.saturating_mul(100) {
                            let right_for_lateral =
                                Self::reorder_joins((*right).clone(), &left_types, cardinality);
                            if is_fit_for_for_loop_join(
                                &right_for_lateral,
                                input_types,
                                &left_types,
                            ) {
                                return GraphPattern::lateral(
                                    left,
                                    GraphPattern::left_join(
                                        GraphPattern::empty_singleton(),
                                        right_for_lateral,
                                        expression,
                                        LeftJoinAlgorithm::HashBuildRightProbeLeft {
                                            keys: Vec::new(),
                                        },
                                    ),
                                );
                            }
                        }
                    }
                }
                let right = Self::reorder_joins(*right, input_types, cardinality);
                let right_types = infer_graph_pattern_types(&right, input_types.clone());
                GraphPattern::left_join(
                    left,
                    right,
                    expression,
                    LeftJoinAlgorithm::HashBuildRightProbeLeft {
                        keys: join_key_variables(&left_types, &right_types, input_types),
                    },
                )
            }
            GraphPattern::Minus { left, right, .. } => {
                let left = Self::reorder_joins(*left, input_types, cardinality);
                let left_types = infer_graph_pattern_types(&left, input_types.clone());
                let right = Self::reorder_joins(*right, input_types, cardinality);
                let right_types = infer_graph_pattern_types(&right, input_types.clone());
                GraphPattern::minus(
                    left,
                    right,
                    MinusAlgorithm::HashBuildRightProbeLeft {
                        keys: join_key_variables(&left_types, &right_types, input_types),
                    },
                )
            }
            GraphPattern::Extend {
                inner,
                expression,
                variable,
            } => GraphPattern::extend(
                Self::reorder_joins(*inner, input_types, cardinality),
                variable,
                expression,
            ),
            GraphPattern::Filter { inner, expression } => GraphPattern::filter(
                Self::reorder_joins(*inner, input_types, cardinality),
                expression,
            ),
            GraphPattern::Union { inner } => GraphPattern::union_all(
                inner
                    .into_iter()
                    .map(|c| Self::reorder_joins(c, input_types, cardinality)),
            ),
            GraphPattern::Slice {
                inner,
                start,
                length,
            } => GraphPattern::slice(
                Self::reorder_joins(*inner, input_types, cardinality),
                start,
                length,
            ),
            GraphPattern::Distinct { inner } => {
                GraphPattern::distinct(Self::reorder_joins(*inner, input_types, cardinality))
            }
            GraphPattern::Reduced { inner } => {
                GraphPattern::reduced(Self::reorder_joins(*inner, input_types, cardinality))
            }
            GraphPattern::Project { inner, variables } => GraphPattern::project(
                Self::reorder_joins(*inner, input_types, cardinality),
                variables,
            ),
            GraphPattern::OrderBy { inner, expression } => GraphPattern::order_by(
                Self::reorder_joins(*inner, input_types, cardinality),
                expression,
            ),
            GraphPattern::Service { .. } => {
                // We don't do join reordering inside of SERVICE calls, we don't know about cardinalities
                pattern
            }
            GraphPattern::Group {
                inner,
                variables,
                aggregates,
            } => GraphPattern::group(
                Self::reorder_joins(*inner, input_types, cardinality),
                variables,
                aggregates,
            ),
        }
    }
}

fn is_fit_for_for_loop_join(
    pattern: &GraphPattern,
    global_input_types: &VariableTypes,
    entry_types: &VariableTypes,
) -> bool {
    // TODO: think more about it
    match pattern {
        GraphPattern::Values { .. }
        | GraphPattern::QuadPattern { .. }
        | GraphPattern::Path { .. }
        | GraphPattern::Graph { .. } => true,
        #[cfg(feature = "sep-0006")]
        GraphPattern::Lateral { left, right } => {
            is_fit_for_for_loop_join(left, global_input_types, entry_types)
                && is_fit_for_for_loop_join(right, global_input_types, entry_types)
        }
        GraphPattern::LeftJoin {
            left,
            right,
            expression,
            ..
        } => {
            if !is_fit_for_for_loop_join(left, global_input_types, entry_types) {
                return false;
            }

            // It is not ok to transform into for loop join if right binds a variable also bound by the entry part of the for loop join
            let mut left_types = infer_graph_pattern_types(left, global_input_types.clone());
            // Keep the global input types for expressions such as BIND(?input AS ?output).
            // Only check variables used by right: other global input bindings pass through unchanged.
            let right_types = infer_graph_pattern_types(right, global_input_types.clone());
            let mut has_conflicting_variable = false;
            right.lookup_used_variables(&mut |variable| {
                has_conflicting_variable |= right_types.get(variable) != VariableType::UNDEF
                    && left_types.get(variable).undef
                    && entry_types.get(variable) != VariableType::UNDEF;
            });
            if has_conflicting_variable {
                return false;
            }

            // We don't forget the final expression
            left_types.intersect_with(right_types);
            is_expression_fit_for_for_loop_join(expression, &left_types, entry_types)
        }
        GraphPattern::Union { inner } => inner
            .iter()
            .all(|i| is_fit_for_for_loop_join(i, global_input_types, entry_types)),
        GraphPattern::Filter { inner, expression } => {
            is_fit_for_for_loop_join(inner, global_input_types, entry_types)
                && is_expression_fit_for_for_loop_join(
                    expression,
                    &infer_graph_pattern_types(inner, global_input_types.clone()),
                    entry_types,
                )
        }
        GraphPattern::Extend {
            inner,
            expression,
            variable,
        } => {
            is_fit_for_for_loop_join(inner, global_input_types, entry_types)
                && entry_types.get(variable) == VariableType::UNDEF
                && is_expression_fit_for_for_loop_join(
                    expression,
                    &infer_graph_pattern_types(inner, global_input_types.clone()),
                    entry_types,
                )
        }
        GraphPattern::Join { .. }
        | GraphPattern::Minus { .. }
        | GraphPattern::Service { .. }
        | GraphPattern::OrderBy { .. }
        | GraphPattern::Distinct { .. }
        | GraphPattern::Reduced { .. }
        | GraphPattern::Slice { .. }
        | GraphPattern::Project { .. }
        | GraphPattern::Group { .. } => false,
    }
}

fn are_all_expression_variables_bound(
    expression: &Expression,
    variable_types: &VariableTypes,
) -> bool {
    expression
        .used_variables()
        .into_iter()
        .all(|v| !variable_types.get(v).undef)
}

fn are_no_expression_variables_bound(
    expression: &Expression,
    variable_types: &VariableTypes,
) -> bool {
    expression
        .used_variables()
        .into_iter()
        .all(|v| variable_types.get(v) == VariableType::UNDEF)
}

fn is_expression_fit_for_for_loop_join(
    expression: &Expression,
    input_types: &VariableTypes,
    entry_types: &VariableTypes,
) -> bool {
    match expression {
        Expression::NamedNode(_) | Expression::Literal(_) => true,
        Expression::Variable(v) | Expression::Bound(v) => {
            !input_types.get(v).undef || entry_types.get(v) == VariableType::UNDEF
        }
        Expression::Or(inner)
        | Expression::And(inner)
        | Expression::Coalesce(inner)
        | Expression::FunctionCall(_, inner) => inner
            .iter()
            .all(|e| is_expression_fit_for_for_loop_join(e, input_types, entry_types)),
        Expression::Equal(a, b)
        | Expression::SameTerm(a, b)
        | Expression::Greater(a, b)
        | Expression::GreaterOrEqual(a, b)
        | Expression::Less(a, b)
        | Expression::LessOrEqual(a, b)
        | Expression::Add(a, b)
        | Expression::Subtract(a, b)
        | Expression::Multiply(a, b)
        | Expression::Divide(a, b) => {
            is_expression_fit_for_for_loop_join(a, input_types, entry_types)
                && is_expression_fit_for_for_loop_join(b, input_types, entry_types)
        }
        Expression::UnaryPlus(e) | Expression::UnaryMinus(e) | Expression::Not(e) => {
            is_expression_fit_for_for_loop_join(e, input_types, entry_types)
        }
        Expression::If(a, b, c) => {
            is_expression_fit_for_for_loop_join(a, input_types, entry_types)
                && is_expression_fit_for_for_loop_join(b, input_types, entry_types)
                && is_expression_fit_for_for_loop_join(c, input_types, entry_types)
        }
        Expression::Exists(inner) => is_fit_for_for_loop_join(inner, input_types, entry_types),
    }
}

fn has_common_variables(
    left: &VariableTypes,
    right: &VariableTypes,
    input_types: &VariableTypes,
) -> bool {
    // TODO: we should be smart and count as shared variables FILTER(?a = ?b)
    left.iter().any(|(variable, left_type)| {
        !left_type.undef && !right.get(variable).undef && input_types.get(variable).undef
    })
}

fn join_key_variables(
    left: &VariableTypes,
    right: &VariableTypes,
    input_types: &VariableTypes,
) -> Vec<Variable> {
    left.iter()
        .filter(|(variable, left_type)| {
            !left_type.undef && !right.get(variable).undef && input_types.get(variable).undef
        })
        .map(|(variable, _)| variable.clone())
        .collect()
}

fn estimate_graph_pattern_size(
    pattern: &GraphPattern,
    input_types: &VariableTypes,
    cardinality: &dyn CardinalityEstimator,
) -> usize {
    match pattern {
        GraphPattern::Values { bindings, .. } => bindings.len(),
        GraphPattern::QuadPattern {
            subject,
            predicate,
            object,
            graph_name,
        } => estimate_quad_pattern_size(
            subject,
            predicate,
            object,
            graph_name.as_ref(),
            input_types,
            cardinality,
        ),
        GraphPattern::Path {
            subject,
            path,
            object,
            ..
        } => estimate_path_size(
            is_term_pattern_bound(subject, input_types),
            path,
            is_term_pattern_bound(object, input_types),
        ),
        GraphPattern::Graph { graph_name } => {
            if is_named_node_pattern_bound(graph_name, input_types) {
                100
            } else {
                1
            }
        }
        GraphPattern::Join {
            left,
            right,
            algorithm,
        } => estimate_join_cost(left, right, algorithm, input_types, cardinality),
        GraphPattern::LeftJoin {
            left,
            right,
            algorithm,
            ..
        } => match algorithm {
            LeftJoinAlgorithm::HashBuildRightProbeLeft { keys } => {
                let left_size = estimate_graph_pattern_size(left, input_types, cardinality);
                max(
                    left_size,
                    left_size
                        .saturating_mul(estimate_graph_pattern_size(
                            right,
                            &infer_graph_pattern_types(right, input_types.clone()),
                            cardinality,
                        ))
                        .saturating_div(1_000_usize.saturating_pow(keys.len().try_into().unwrap())),
                )
            }
        },
        #[cfg(feature = "sep-0006")]
        GraphPattern::Lateral { left, right } => estimate_lateral_cost(
            left,
            &infer_graph_pattern_types(left, input_types.clone()),
            right,
            input_types,
            cardinality,
        ),
        GraphPattern::Union { inner } => inner
            .iter()
            .map(|inner| estimate_graph_pattern_size(inner, input_types, cardinality))
            .fold(0, usize::saturating_add),
        GraphPattern::Minus { left, .. } => {
            estimate_graph_pattern_size(left, input_types, cardinality)
        }
        GraphPattern::Filter { inner, .. }
        | GraphPattern::Extend { inner, .. }
        | GraphPattern::OrderBy { inner, .. }
        | GraphPattern::Project { inner, .. }
        | GraphPattern::Distinct { inner, .. }
        | GraphPattern::Reduced { inner, .. }
        | GraphPattern::Group { inner, .. }
        | GraphPattern::Service { inner, .. } => {
            estimate_graph_pattern_size(inner, input_types, cardinality)
        }
        GraphPattern::Slice {
            inner,
            start,
            length,
        } => {
            let inner =
                estimate_graph_pattern_size(inner, input_types, cardinality).saturating_sub(*start);
            if let Some(length) = length {
                min(inner, *length)
            } else {
                inner
            }
        }
    }
}

fn estimate_join_cost(
    left: &GraphPattern,
    right: &GraphPattern,
    algorithm: &JoinAlgorithm,
    input_types: &VariableTypes,
    cardinality: &dyn CardinalityEstimator,
) -> usize {
    match algorithm {
        JoinAlgorithm::HashBuildLeftProbeRight { keys } => {
            estimate_graph_pattern_size(left, input_types, cardinality)
                .saturating_mul(estimate_graph_pattern_size(right, input_types, cardinality))
                .saturating_div(1_000_usize.saturating_pow(keys.len().try_into().unwrap()))
        }
    }
}

fn estimate_lateral_cost(
    left: &GraphPattern,
    left_types: &VariableTypes,
    right: &GraphPattern,
    input_types: &VariableTypes,
    cardinality: &dyn CardinalityEstimator,
) -> usize {
    estimate_graph_pattern_size(left, input_types, cardinality)
        .saturating_mul(estimate_graph_pattern_size(right, left_types, cardinality))
}

/// Size of one quad pattern, preferring the store's own count over the shape-based guess.
///
/// The estimator only knows about the pattern's constants, so its answer has to be adjusted for
/// the positions the input will bind: the shape table's ratio between "what the input will bind"
/// and "constants only" is exactly that adjustment, and applying it leaves the measured count
/// untouched when the input binds nothing new.
fn estimate_quad_pattern_size(
    subject: &GroundTermPattern,
    predicate: &NamedNodePattern,
    object: &GroundTermPattern,
    graph_name: Option<&NamedNodePattern>,
    input_types: &VariableTypes,
    cardinality: &dyn CardinalityEstimator,
) -> usize {
    let shape = estimate_triple_pattern_size(
        is_term_pattern_bound(subject, input_types),
        is_named_node_pattern_bound(predicate, input_types),
        is_term_pattern_bound(object, input_types),
    );
    let Some(measured) = cardinality.quad_pattern_size(
        term_pattern_constant(subject),
        named_node_pattern_constant(predicate),
        term_pattern_constant(object),
        graph_name_constant(graph_name),
    ) else {
        // With only the shape to go on, an `rdf:type` pattern scores one more than any other of
        // its shape, so that of two otherwise tied patterns it is joined later.
        if let NamedNodePattern::NamedNode(predicate) = predicate {
            if *predicate == rdf::TYPE {
                return shape.saturating_add(1);
            }
        }
        return shape;
    };
    if measured == 0 {
        return 0;
    }
    let constants_shape = estimate_triple_pattern_size(
        term_pattern_constant(subject).is_some(),
        named_node_pattern_constant(predicate).is_some(),
        term_pattern_constant(object).is_some(),
    );
    // At least 1: a pattern the store says matches something must not look free.
    max(1, measured.saturating_mul(shape) / constants_shape)
}

/// The term at a pattern position when it is a constant, `None` when it is a variable.
///
/// Quoted triples are always `None`: a store asked for a cardinality cannot be handed one through
/// this interface, and a pattern containing one is rare enough not to be worth widening it for.
fn term_pattern_constant(pattern: &GroundTermPattern) -> Option<TermRef<'_>> {
    match pattern {
        GroundTermPattern::NamedNode(term) => Some(term.as_ref().into()),
        GroundTermPattern::Literal(term) => Some(term.as_ref().into()),
        GroundTermPattern::Variable(_) => None,
        #[cfg(feature = "sparql-12")]
        GroundTermPattern::Triple(_) => None,
    }
}

fn named_node_pattern_constant(pattern: &NamedNodePattern) -> Option<NamedNodeRef<'_>> {
    match pattern {
        NamedNodePattern::NamedNode(node) => Some(node.as_ref()),
        NamedNodePattern::Variable(_) => None,
    }
}

/// Encoded the way [`CardinalityEstimator`] expects: `Some(None)` for the default graph,
/// `Some(Some(iri))` for one named graph, and `None` when the graph is itself a variable.
fn graph_name_constant(pattern: Option<&NamedNodePattern>) -> Option<Option<NamedNodeRef<'_>>> {
    match pattern {
        None => Some(None),
        Some(NamedNodePattern::NamedNode(node)) => Some(Some(node.as_ref())),
        Some(NamedNodePattern::Variable(_)) => None,
    }
}

fn estimate_triple_pattern_size(
    subject_bound: bool,
    predicate_bound: bool,
    object_bound: bool,
) -> usize {
    match (subject_bound, predicate_bound, object_bound) {
        (true, true, true) => 1,
        (true, true, false) => 10,
        (true, false, true) => 2,
        (false, true, true) => 1_000,
        (true, false, false) => 100,
        (false, false, false) => 1_000_000_000,
        (false, true, false) => 1_000_000,
        (false, false, true) => 10_000,
    }
}

fn estimate_path_size(start_bound: bool, path: &PropertyPathExpression, end_bound: bool) -> usize {
    match path {
        PropertyPathExpression::NamedNode(_) => {
            estimate_triple_pattern_size(start_bound, true, end_bound)
        }
        PropertyPathExpression::Reverse(p) => estimate_path_size(end_bound, p, start_bound),
        PropertyPathExpression::Sequence(a, b) => {
            // We do a for loop join in the best direction
            min(
                estimate_path_size(start_bound, a, false)
                    .saturating_mul(estimate_path_size(true, b, end_bound)),
                estimate_path_size(start_bound, a, true)
                    .saturating_mul(estimate_path_size(false, b, end_bound)),
            )
        }
        PropertyPathExpression::Alternative(a, b) => estimate_path_size(start_bound, a, end_bound)
            .saturating_add(estimate_path_size(start_bound, b, end_bound)),
        PropertyPathExpression::ZeroOrMore(p) => {
            if start_bound && end_bound {
                1
            } else if start_bound || end_bound {
                estimate_path_size(start_bound, p, end_bound).saturating_mul(1000)
            } else {
                1_000_000_000
            }
        }
        PropertyPathExpression::OneOrMore(p) => {
            if start_bound && end_bound {
                1
            } else {
                estimate_path_size(start_bound, p, end_bound).saturating_mul(1000)
            }
        }
        PropertyPathExpression::ZeroOrOne(p) => {
            if start_bound && end_bound {
                1
            } else if start_bound || end_bound {
                estimate_path_size(start_bound, p, end_bound)
            } else {
                1_000_000_000
            }
        }
        PropertyPathExpression::NegatedPropertySet(_) => {
            estimate_triple_pattern_size(start_bound, false, end_bound)
        }
    }
}

fn is_term_pattern_bound(pattern: &GroundTermPattern, input_types: &VariableTypes) -> bool {
    match pattern {
        GroundTermPattern::NamedNode(_) | GroundTermPattern::Literal(_) => true,
        GroundTermPattern::Variable(v) => !input_types.get(v).undef,
        #[cfg(feature = "sparql-12")]
        GroundTermPattern::Triple(t) => {
            is_term_pattern_bound(&t.subject, input_types)
                && is_named_node_pattern_bound(&t.predicate, input_types)
                && is_term_pattern_bound(&t.object, input_types)
        }
    }
}

fn is_named_node_pattern_bound(pattern: &NamedNodePattern, input_types: &VariableTypes) -> bool {
    match pattern {
        NamedNodePattern::NamedNode(_) => true,
        NamedNodePattern::Variable(v) => !input_types.get(v).undef,
    }
}
