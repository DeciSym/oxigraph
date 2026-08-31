//! [SPARQL 1.1 Query Algebra](https://www.w3.org/TR/sparql11-query/#sparqlQuery) representation.

use oxrdf::vocab::xsd;
use rand::random;
use spargebra::algebra::{
    AggregateExpression as AlAggregateExpression, AggregateFunction, Expression as AlExpression,
    GraphPattern as AlGraphPattern, OrderExpression as AlOrderExpression,
};
pub use spargebra::algebra::{Function, PropertyPathExpression};
use spargebra::term::{BlankNode, TermPattern, TriplePattern};
pub use spargebra::term::{
    GroundTerm, GroundTermPattern, Literal, NamedNode, NamedNodePattern, Variable,
};
#[cfg(feature = "sparql-12")]
use spargebra::term::{GroundTriple, GroundTriplePattern};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::ops::{Add, BitAnd, BitOr, Div, Mul, Neg, Not, Sub};
use std::slice;

/// An [expression](https://www.w3.org/TR/sparql11-query/#expressions).
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub enum Expression {
    NamedNode(NamedNode),
    Literal(Literal),
    Variable(Variable),
    /// [Logical-or](https://www.w3.org/TR/sparql11-query/#func-logical-or).
    Or(Vec<Self>),
    /// [Logical-and](https://www.w3.org/TR/sparql11-query/#func-logical-and).
    And(Vec<Self>),
    /// [RDFterm-equal](https://www.w3.org/TR/sparql11-query/#func-RDFterm-equal) and all the XSD equalities.
    Equal(Box<Self>, Box<Self>),
    /// [sameTerm](https://www.w3.org/TR/sparql11-query/#func-sameTerm).
    SameTerm(Box<Self>, Box<Self>),
    /// [op:numeric-greater-than](https://www.w3.org/TR/xpath-functions-31/#func-numeric-greater-than) and other XSD greater than operators.
    Greater(Box<Self>, Box<Self>),
    GreaterOrEqual(Box<Self>, Box<Self>),
    /// [op:numeric-less-than](https://www.w3.org/TR/xpath-functions-31/#func-numeric-less-than) and other XSD greater than operators.
    Less(Box<Self>, Box<Self>),
    LessOrEqual(Box<Self>, Box<Self>),
    /// [op:numeric-add](https://www.w3.org/TR/xpath-functions-31/#func-numeric-add) and other XSD additions.
    Add(Box<Self>, Box<Self>),
    /// [op:numeric-subtract](https://www.w3.org/TR/xpath-functions-31/#func-numeric-subtract) and other XSD subtractions.
    Subtract(Box<Self>, Box<Self>),
    /// [op:numeric-multiply](https://www.w3.org/TR/xpath-functions-31/#func-numeric-multiply) and other XSD multiplications.
    Multiply(Box<Self>, Box<Self>),
    /// [op:numeric-divide](https://www.w3.org/TR/xpath-functions-31/#func-numeric-divide) and other XSD divides.
    Divide(Box<Self>, Box<Self>),
    /// [op:numeric-unary-plus](https://www.w3.org/TR/xpath-functions-31/#func-numeric-unary-plus) and other XSD unary plus.
    UnaryPlus(Box<Self>),
    /// [op:numeric-unary-minus](https://www.w3.org/TR/xpath-functions-31/#func-numeric-unary-minus) and other XSD unary minus.
    UnaryMinus(Box<Self>),
    /// [fn:not](https://www.w3.org/TR/xpath-functions-31/#func-not).
    Not(Box<Self>),
    /// [EXISTS](https://www.w3.org/TR/sparql11-query/#func-filter-exists).
    Exists(Box<GraphPattern>),
    /// [BOUND](https://www.w3.org/TR/sparql11-query/#func-bound).
    Bound(Variable),
    /// [IF](https://www.w3.org/TR/sparql11-query/#func-if).
    If(Box<Self>, Box<Self>, Box<Self>),
    /// [COALESCE](https://www.w3.org/TR/sparql11-query/#func-coalesce).
    Coalesce(Vec<Self>),
    /// A regular function call.
    FunctionCall(Function, Vec<Self>),
}

impl Expression {
    pub fn or_all(args: impl IntoIterator<Item = Self>) -> Self {
        let args = args.into_iter();
        let mut all = Vec::with_capacity(args.size_hint().0);
        for arg in args {
            if let Some(ebv) = arg.effective_boolean_value() {
                if ebv {
                    return true.into();
                }
                // We ignore false values
            } else if let Self::Or(args) = arg {
                all.extend(args);
            } else {
                all.push(arg);
            }
        }
        match all.len() {
            0 => false.into(),
            1 => {
                let result = all.pop().unwrap();
                if result.returns_boolean() {
                    result // It's already casted to boolean
                } else {
                    Self::And(vec![result])
                }
            }
            _ => Self::Or(order_vec(all)),
        }
    }

    pub fn and_all(args: impl IntoIterator<Item = Self>) -> Self {
        let args = args.into_iter();
        let mut all = Vec::with_capacity(args.size_hint().0);
        for arg in args {
            if let Some(ebv) = arg.effective_boolean_value() {
                if !ebv {
                    return false.into();
                }
                // We ignore true values
            } else if let Self::And(args) = arg {
                all.extend(args);
            } else {
                all.push(arg);
            }
        }
        match all.len() {
            0 => true.into(),
            1 => {
                let result = all.pop().unwrap();
                if result.returns_boolean() {
                    result
                } else {
                    Self::And(vec![result])
                }
            }
            _ => Self::And(order_vec(all)),
        }
    }

    pub fn equal(left: Self, right: Self) -> Self {
        // TODO: simplify equality when both operands are literal taking care of fun stuff like NaN != NaN
        match (left, right) {
            (Self::NamedNode(left), Self::NamedNode(right)) => (left == right).into(),
            (left, right) => {
                let (left, right) = order_pair(left, right);
                Self::Equal(Box::new(left), Box::new(right))
            }
        }
    }

    pub fn same_term(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::NamedNode(left), Self::NamedNode(right)) => (left == right).into(),
            (Self::Literal(left), Self::Literal(right)) if left == right => true.into(),
            (left, right) => {
                let (left, right) = order_pair(left, right);
                Self::SameTerm(Box::new(left), Box::new(right))
            }
        }
    }

    pub fn greater(left: Self, right: Self) -> Self {
        Self::Greater(Box::new(left), Box::new(right))
    }

    pub fn greater_or_equal(left: Self, right: Self) -> Self {
        Self::GreaterOrEqual(Box::new(left), Box::new(right))
    }

    pub fn less(left: Self, right: Self) -> Self {
        Self::Less(Box::new(left), Box::new(right))
    }

    pub fn less_or_equal(left: Self, right: Self) -> Self {
        Self::LessOrEqual(Box::new(left), Box::new(right))
    }

    pub fn unary_plus(inner: Self) -> Self {
        Self::UnaryPlus(Box::new(inner))
    }

    pub fn exists(inner: GraphPattern) -> Self {
        if inner.is_empty() {
            return false.into();
        }
        if inner.is_empty_singleton() {
            return true.into();
        }
        Self::Exists(Box::new(inner))
    }

    pub fn if_cond(cond: Self, then: Self, els: Self) -> Self {
        match cond.effective_boolean_value() {
            Some(true) => then,
            Some(false) => els,
            None => Self::If(Box::new(cond), Box::new(then), Box::new(els)),
        }
    }

    pub fn coalesce(args: Vec<Self>) -> Self {
        Self::Coalesce(args)
    }

    pub fn call(name: Function, args: Vec<Self>) -> Self {
        Self::FunctionCall(name, args)
    }

    pub fn effective_boolean_value(&self) -> Option<bool> {
        if let Self::Literal(literal) = self {
            match literal.datatype() {
                xsd::BOOLEAN => match literal.value() {
                    "true" | "1" => Some(true),
                    "false" | "0" => Some(false),
                    _ => None, // TODO
                },
                xsd::STRING => Some(!literal.value().is_empty()),
                _ => None, // TODO
            }
        } else {
            None
        }
    }

    pub fn used_variables(&self) -> HashSet<&Variable> {
        let mut variables = HashSet::new();
        self.lookup_used_variables(&mut |v| {
            variables.insert(v);
        });
        variables
    }

    pub fn lookup_used_variables<'a>(&'a self, callback: &mut impl FnMut(&'a Variable)) {
        match self {
            Self::NamedNode(_) | Self::Literal(_) => {}
            Self::Variable(v) | Self::Bound(v) => callback(v),
            Self::Or(inner)
            | Self::And(inner)
            | Self::Coalesce(inner)
            | Self::FunctionCall(_, inner) => {
                for i in inner {
                    i.lookup_used_variables(callback);
                }
            }
            Self::Equal(a, b)
            | Self::SameTerm(a, b)
            | Self::Greater(a, b)
            | Self::GreaterOrEqual(a, b)
            | Self::Less(a, b)
            | Self::LessOrEqual(a, b)
            | Self::Add(a, b)
            | Self::Subtract(a, b)
            | Self::Multiply(a, b)
            | Self::Divide(a, b) => {
                a.lookup_used_variables(callback);
                b.lookup_used_variables(callback);
            }
            Self::UnaryPlus(i) | Self::UnaryMinus(i) | Self::Not(i) => {
                i.lookup_used_variables(callback)
            }
            Self::Exists(e) => e.lookup_used_variables(callback),
            Self::If(a, b, c) => {
                a.lookup_used_variables(callback);
                b.lookup_used_variables(callback);
                c.lookup_used_variables(callback);
            }
        }
    }

    fn from_sparql_algebra(
        expression: &AlExpression,
        graph_name: Option<&NamedNodePattern>,
    ) -> Self {
        match expression {
            AlExpression::NamedNode(node) => Self::NamedNode(node.clone()),
            AlExpression::Literal(literal) => Self::Literal(literal.clone()),
            AlExpression::Variable(variable) => Self::Variable(variable.clone()),
            AlExpression::Or(left, right) => Self::Or(vec![
                Self::from_sparql_algebra(left, graph_name),
                Self::from_sparql_algebra(right, graph_name),
            ]),
            AlExpression::And(left, right) => Self::And(vec![
                Self::from_sparql_algebra(left, graph_name),
                Self::from_sparql_algebra(right, graph_name),
            ]),
            AlExpression::Equal(left, right) => Self::Equal(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::SameTerm(left, right) => Self::SameTerm(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::Greater(left, right) => Self::Greater(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::GreaterOrEqual(left, right) => Self::GreaterOrEqual(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::Less(left, right) => Self::Less(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::LessOrEqual(left, right) => Self::LessOrEqual(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::In(left, right) => {
                let left = Self::from_sparql_algebra(left, graph_name);
                match right.len() {
                    0 => Self::if_cond(left, false.into(), false.into()),
                    1 => Self::Equal(
                        Box::new(left),
                        Box::new(Self::from_sparql_algebra(&right[0], graph_name)),
                    ),
                    _ => Self::Or(
                        right
                            .iter()
                            .map(|e| {
                                Self::Equal(
                                    Box::new(left.clone()),
                                    Box::new(Self::from_sparql_algebra(e, graph_name)),
                                )
                            })
                            .collect(),
                    ),
                }
            }
            AlExpression::Add(left, right) => Self::Add(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::Subtract(left, right) => Self::Subtract(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::Multiply(left, right) => Self::Multiply(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::Divide(left, right) => Self::Divide(
                Box::new(Self::from_sparql_algebra(left, graph_name)),
                Box::new(Self::from_sparql_algebra(right, graph_name)),
            ),
            AlExpression::UnaryPlus(inner) => {
                Self::UnaryPlus(Box::new(Self::from_sparql_algebra(inner, graph_name)))
            }
            AlExpression::UnaryMinus(inner) => {
                Self::UnaryMinus(Box::new(Self::from_sparql_algebra(inner, graph_name)))
            }
            AlExpression::Not(inner) => {
                Self::Not(Box::new(Self::from_sparql_algebra(inner, graph_name)))
            }
            AlExpression::Exists(inner) => Self::Exists(Box::new(
                GraphPattern::from_sparql_algebra(inner, graph_name, &mut HashMap::new()),
            )),
            AlExpression::Bound(variable) => Self::Bound(variable.clone()),
            AlExpression::If(cond, yes, no) => Self::If(
                Box::new(Self::from_sparql_algebra(cond, graph_name)),
                Box::new(Self::from_sparql_algebra(yes, graph_name)),
                Box::new(Self::from_sparql_algebra(no, graph_name)),
            ),
            AlExpression::Coalesce(inner) => Self::Coalesce(
                inner
                    .iter()
                    .map(|e| Self::from_sparql_algebra(e, graph_name))
                    .collect(),
            ),
            AlExpression::FunctionCall(name, args) => Self::FunctionCall(
                name.clone(),
                args.iter()
                    .map(|e| Self::from_sparql_algebra(e, graph_name))
                    .collect(),
            ),
        }
    }

    fn returns_boolean(&self) -> bool {
        match self {
            Self::Or(_)
            | Self::And(_)
            | Self::Equal(_, _)
            | Self::SameTerm(_, _)
            | Self::Greater(_, _)
            | Self::GreaterOrEqual(_, _)
            | Self::Less(_, _)
            | Self::LessOrEqual(_, _)
            | Self::Not(_)
            | Self::Exists(_)
            | Self::Bound(_)
            | Self::FunctionCall(
                Function::IsBlank | Function::IsIri | Function::IsLiteral | Function::IsNumeric,
                _,
            ) => true,
            #[cfg(feature = "sparql-12")]
            Self::FunctionCall(Function::IsTriple, _) => true,
            Self::Literal(literal) => literal.datatype() == xsd::BOOLEAN,
            Self::If(_, a, b) => a.returns_boolean() && b.returns_boolean(),
            _ => false,
        }
    }
}

impl From<NamedNode> for Expression {
    fn from(value: NamedNode) -> Self {
        Self::NamedNode(value)
    }
}

impl From<Literal> for Expression {
    fn from(value: Literal) -> Self {
        Self::Literal(value)
    }
}

impl From<GroundTerm> for Expression {
    fn from(value: GroundTerm) -> Self {
        match value {
            GroundTerm::NamedNode(value) => value.into(),
            GroundTerm::Literal(value) => value.into(),
            #[cfg(feature = "sparql-12")]
            GroundTerm::Triple(value) => (*value).into(),
        }
    }
}

impl From<NamedNodePattern> for Expression {
    fn from(value: NamedNodePattern) -> Self {
        match value {
            NamedNodePattern::NamedNode(value) => value.into(),
            NamedNodePattern::Variable(variable) => variable.into(),
        }
    }
}

impl From<GroundTermPattern> for Expression {
    fn from(value: GroundTermPattern) -> Self {
        match value {
            GroundTermPattern::NamedNode(value) => value.into(),
            GroundTermPattern::Literal(value) => value.into(),
            #[cfg(feature = "sparql-12")]
            GroundTermPattern::Triple(value) => (*value).into(),
            GroundTermPattern::Variable(variable) => variable.into(),
        }
    }
}

#[cfg(feature = "sparql-12")]
impl From<GroundTriple> for Expression {
    fn from(value: GroundTriple) -> Self {
        Self::FunctionCall(
            Function::Triple,
            vec![
                value.subject.into(),
                value.predicate.into(),
                value.object.into(),
            ],
        )
    }
}

#[cfg(feature = "sparql-12")]
impl From<GroundTriplePattern> for Expression {
    fn from(value: GroundTriplePattern) -> Self {
        Self::FunctionCall(
            Function::Triple,
            vec![
                value.subject.into(),
                value.predicate.into(),
                value.object.into(),
            ],
        )
    }
}

impl From<Variable> for Expression {
    fn from(value: Variable) -> Self {
        Self::Variable(value)
    }
}

impl From<bool> for Expression {
    fn from(value: bool) -> Self {
        Literal::from(value).into()
    }
}

impl From<&Expression> for AlExpression {
    fn from(expression: &Expression) -> Self {
        match expression {
            Expression::NamedNode(node) => Self::NamedNode(node.clone()),
            Expression::Literal(literal) => Self::Literal(literal.clone()),
            Expression::Variable(variable) => Self::Variable(variable.clone()),
            Expression::Or(inner) => inner
                .iter()
                .map(Into::into)
                .reduce(|a, b| Self::Or(Box::new(a), Box::new(b)))
                .unwrap_or_else(|| Literal::from(false).into()),
            Expression::And(inner) => inner
                .iter()
                .map(Into::into)
                .reduce(|a, b| Self::And(Box::new(a), Box::new(b)))
                .unwrap_or_else(|| Literal::from(true).into()),
            Expression::Equal(left, right) => Self::Equal(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::SameTerm(left, right) => Self::SameTerm(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::Greater(left, right) => Self::Greater(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::GreaterOrEqual(left, right) => Self::GreaterOrEqual(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::Less(left, right) => Self::Less(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::LessOrEqual(left, right) => Self::LessOrEqual(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::Add(left, right) => Self::Add(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::Subtract(left, right) => Self::Subtract(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::Multiply(left, right) => Self::Multiply(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::Divide(left, right) => Self::Divide(
                Box::new(left.as_ref().into()),
                Box::new(right.as_ref().into()),
            ),
            Expression::UnaryPlus(inner) => Self::UnaryPlus(Box::new(inner.as_ref().into())),
            Expression::UnaryMinus(inner) => Self::UnaryMinus(Box::new(inner.as_ref().into())),
            Expression::Not(inner) => Self::Not(Box::new(inner.as_ref().into())),
            Expression::Exists(inner) => Self::Exists(Box::new(inner.as_ref().into())),
            Expression::Bound(variable) => Self::Bound(variable.clone()),
            Expression::If(cond, yes, no) => Self::If(
                Box::new(cond.as_ref().into()),
                Box::new(yes.as_ref().into()),
                Box::new(no.as_ref().into()),
            ),
            Expression::Coalesce(inner) => Self::Coalesce(inner.iter().map(Into::into).collect()),
            Expression::FunctionCall(name, args) => {
                Self::FunctionCall(name.clone(), args.iter().map(Into::into).collect())
            }
        }
    }
}

impl BitAnd for Expression {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::and_all([self, rhs])
    }
}

impl BitOr for Expression {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        Self::or_all([self, rhs])
    }
}

impl Not for Expression {
    type Output = Self;

    fn not(self) -> Self {
        if let Some(v) = self.effective_boolean_value() {
            (!v).into()
        } else if let Self::Not(v) = self {
            if v.returns_boolean() {
                *v
            } else {
                Self::Not(Box::new(Self::Not(v)))
            }
        } else {
            Self::Not(Box::new(self))
        }
    }
}

impl Add for Expression {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let (left, right) = order_pair(self, rhs);
        Self::Add(Box::new(left), Box::new(right))
    }
}

impl Sub for Expression {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self::Subtract(Box::new(self), Box::new(rhs))
    }
}

impl Mul for Expression {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let (left, right) = order_pair(self, rhs);
        Self::Multiply(Box::new(left), Box::new(right))
    }
}

impl Div for Expression {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        Self::Divide(Box::new(self), Box::new(rhs))
    }
}

impl Neg for Expression {
    type Output = Self;

    fn neg(self) -> Self {
        Self::UnaryMinus(Box::new(self))
    }
}

/// A SPARQL query [graph pattern](https://www.w3.org/TR/sparql11-query/#sparqlQuery).
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub enum GraphPattern {
    /// A [basic graph pattern](https://www.w3.org/TR/sparql11-query/#defn_BasicGraphPattern).
    QuadPattern {
        subject: GroundTermPattern,
        predicate: NamedNodePattern,
        object: GroundTermPattern,
        graph_name: Option<NamedNodePattern>, // None for the default graph
    },
    /// A [property path pattern](https://www.w3.org/TR/sparql11-query/#defn_evalPP_predicate).
    Path {
        subject: GroundTermPattern,
        path: PropertyPathExpression,
        object: GroundTermPattern,
        graph_name: Option<NamedNodePattern>, // None for the default graph
    },
    /// Graph check
    ///
    /// Can yield all named graph like in `GRAPH ?g {}`
    /// or only check if a graph exist like in `GRAPH ex:g {}`
    Graph { graph_name: NamedNodePattern },
    /// [Join](https://www.w3.org/TR/sparql11-query/#defn_algJoin).
    Join {
        left: Box<Self>,
        right: Box<Self>,
        algorithm: JoinAlgorithm,
    },
    /// [LeftJoin](https://www.w3.org/TR/sparql11-query/#defn_algLeftJoin).
    LeftJoin {
        left: Box<Self>,
        right: Box<Self>,
        expression: Expression,
        algorithm: LeftJoinAlgorithm,
    },
    /// Lateral join i.e. evaluate right for all result row of left
    #[cfg(feature = "sep-0006")]
    Lateral { left: Box<Self>, right: Box<Self> },
    /// [Filter](https://www.w3.org/TR/sparql11-query/#defn_algFilter).
    Filter {
        expression: Expression,
        inner: Box<Self>,
    },
    /// [Union](https://www.w3.org/TR/sparql11-query/#defn_algUnion).
    Union { inner: Vec<Self> },
    /// [Extend](https://www.w3.org/TR/sparql11-query/#defn_extend).
    Extend {
        inner: Box<Self>,
        variable: Variable,
        expression: Expression,
    },
    /// [Minus](https://www.w3.org/TR/sparql11-query/#defn_algMinus).
    Minus {
        left: Box<Self>,
        right: Box<Self>,
        algorithm: MinusAlgorithm,
    },
    /// A table used to provide inline values
    Values {
        variables: Vec<Variable>,
        bindings: Vec<Vec<Option<GroundTerm>>>,
    },
    /// [OrderBy](https://www.w3.org/TR/sparql11-query/#defn_algOrdered).
    OrderBy {
        inner: Box<Self>,
        expression: Vec<OrderExpression>,
    },
    /// [Project](https://www.w3.org/TR/sparql11-query/#defn_algProjection).
    Project {
        inner: Box<Self>,
        variables: Vec<Variable>,
    },
    /// [Distinct](https://www.w3.org/TR/sparql11-query/#defn_algDistinct).
    Distinct { inner: Box<Self> },
    /// [Reduced](https://www.w3.org/TR/sparql11-query/#defn_algReduced).
    Reduced { inner: Box<Self> },
    /// [Slice](https://www.w3.org/TR/sparql11-query/#defn_algSlice).
    Slice {
        inner: Box<Self>,
        start: usize,
        length: Option<usize>,
    },
    /// [Group](https://www.w3.org/TR/sparql11-query/#aggregateAlgebra).
    Group {
        inner: Box<Self>,
        variables: Vec<Variable>,
        aggregates: Vec<(Variable, AggregateExpression)>,
    },
    /// [Service](https://www.w3.org/TR/sparql11-federated-query/#defn_evalService).
    Service {
        name: NamedNodePattern,
        inner: Box<Self>,
        silent: bool,
    },
}

impl GraphPattern {
    pub fn empty() -> Self {
        Self::Values {
            variables: Vec::new(),
            bindings: Vec::new(),
        }
    }

    /// Check if the pattern is the empty table
    fn is_empty(&self) -> bool {
        if let Self::Values { bindings, .. } = self {
            bindings.is_empty()
        } else {
            false
        }
    }

    pub fn empty_singleton() -> Self {
        Self::Values {
            variables: Vec::new(),
            bindings: vec![Vec::new()],
        }
    }

    pub fn is_empty_singleton(&self) -> bool {
        if let Self::Values { bindings, .. } = self {
            bindings.len() == 1 && bindings.iter().all(|b| b.iter().all(Option::is_none))
        } else {
            false
        }
    }

    pub fn join(left: Self, right: Self, algorithm: JoinAlgorithm) -> Self {
        if left.is_empty() || right.is_empty() {
            return Self::empty();
        }
        if left.is_empty_singleton() {
            return right;
        }
        if right.is_empty_singleton() {
            return left;
        }
        Self::Join {
            left: Box::new(left),
            right: Box::new(right),
            algorithm,
        }
    }

    #[cfg(feature = "sep-0006")]
    pub fn lateral(left: Self, right: Self) -> Self {
        if left.is_empty() || right.is_empty() {
            return Self::empty();
        }
        if left.is_empty_singleton() {
            return right;
        }
        if right.is_empty_singleton() {
            return left;
        }
        Self::Lateral {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn left_join(
        left: Self,
        right: Self,
        expression: Expression,
        algorithm: LeftJoinAlgorithm,
    ) -> Self {
        let expression_ebv = expression.effective_boolean_value();
        if left.is_empty()
            || right.is_empty()
            || right.is_empty_singleton()
            || expression_ebv == Some(false)
        {
            return left;
        }
        Self::LeftJoin {
            left: Box::new(left),
            right: Box::new(right),
            expression: if expression_ebv == Some(true) {
                true.into()
            } else {
                expression
            },
            algorithm,
        }
    }

    pub fn minus(left: Self, right: Self, algorithm: MinusAlgorithm) -> Self {
        if left.is_empty() {
            return Self::empty();
        }
        if right.is_empty() {
            return left;
        }
        Self::Minus {
            left: Box::new(left),
            right: Box::new(right),
            algorithm,
        }
    }

    pub fn union(left: Self, right: Self) -> Self {
        Self::union_all([left, right])
    }

    pub fn union_all(args: impl IntoIterator<Item = Self>) -> Self {
        let args = args.into_iter();
        let mut all = Vec::with_capacity(args.size_hint().0);
        for arg in args {
            if arg.is_empty() {
                continue;
            }
            if let Self::Union { inner } = arg {
                all.extend(inner);
            } else {
                all.push(arg);
            }
        }
        if all.is_empty() {
            Self::empty()
        } else {
            Self::Union {
                inner: order_vec(all),
            }
        }
    }

    pub fn filter(inner: Self, expression: Expression) -> Self {
        if inner.is_empty() {
            return Self::empty();
        }
        // We unwrap singleton And
        let expression = match expression {
            Expression::And(mut l) if l.len() == 1 => l.pop().unwrap(),
            e => e,
        };
        match expression.effective_boolean_value() {
            Some(true) => inner,
            Some(false) => Self::empty(),
            None => match inner {
                Self::Filter {
                    inner: nested_inner,
                    expression: e2,
                } => Self::Filter {
                    inner: nested_inner,
                    expression: expression & e2,
                },
                _ => Self::Filter {
                    inner: Box::new(inner),
                    expression,
                },
            },
        }
    }

    pub fn extend(inner: Self, variable: Variable, expression: Expression) -> Self {
        if inner.is_empty() {
            return Self::empty();
        }
        Self::Extend {
            inner: Box::new(inner),
            variable,
            expression,
        }
    }

    pub fn values(
        mut variables: Vec<Variable>,
        mut bindings: Vec<Vec<Option<GroundTerm>>>,
    ) -> Self {
        let empty_rows = (0..variables.len())
            .filter(|row| !bindings.iter().any(|binding| binding.get(*row).is_some()))
            .collect::<Vec<_>>();
        if !empty_rows.is_empty() {
            // We remove empty rows
            variables = variables
                .into_iter()
                .enumerate()
                .filter_map(|(i, v)| {
                    if empty_rows.contains(&i) {
                        None
                    } else {
                        Some(v)
                    }
                })
                .collect();
            bindings = bindings
                .into_iter()
                .map(|binding| {
                    binding
                        .into_iter()
                        .enumerate()
                        .filter_map(|(i, v)| {
                            if empty_rows.contains(&i) {
                                None
                            } else {
                                Some(v)
                            }
                        })
                        .collect()
                })
                .collect();
        }
        Self::Values {
            variables,
            bindings,
        }
    }

    pub fn order_by(inner: Self, expression: Vec<OrderExpression>) -> Self {
        if inner.is_empty() {
            return Self::empty();
        }
        if expression.is_empty() {
            return inner;
        }
        Self::OrderBy {
            inner: Box::new(inner),
            expression,
        }
    }

    pub fn project(inner: Self, variables: Vec<Variable>) -> Self {
        Self::Project {
            inner: Box::new(inner),
            variables,
        }
    }

    pub fn distinct(inner: Self) -> Self {
        if inner.is_empty() {
            return Self::empty();
        }
        Self::Distinct {
            inner: Box::new(inner),
        }
    }

    pub fn reduced(inner: Self) -> Self {
        if inner.is_empty() {
            return Self::empty();
        }
        Self::Reduced {
            inner: Box::new(inner),
        }
    }

    pub fn slice(inner: Self, start: usize, length: Option<usize>) -> Self {
        if inner.is_empty() {
            return Self::empty();
        }
        if start == 0 && length.is_none() {
            return inner;
        }
        Self::Slice {
            inner: Box::new(inner),
            start,
            length,
        }
    }

    pub fn group(
        inner: Self,
        variables: Vec<Variable>,
        aggregates: Vec<(Variable, AggregateExpression)>,
    ) -> Self {
        if inner.is_empty() {
            return Self::empty();
        }
        Self::Group {
            inner: Box::new(inner),
            variables,
            aggregates,
        }
    }

    pub fn service(inner: Self, name: NamedNodePattern, silent: bool) -> Self {
        Self::Service {
            inner: Box::new(inner),
            name,
            silent,
        }
    }

    pub fn lookup_used_variables<'a>(&'a self, callback: &mut impl FnMut(&'a Variable)) {
        match self {
            Self::Values { variables, .. } | Self::Project { variables, .. } => {
                for v in variables {
                    callback(v);
                }
            }
            Self::QuadPattern {
                subject,
                predicate,
                object,
                graph_name,
            } => {
                lookup_term_pattern_variables(subject, callback);
                if let NamedNodePattern::Variable(v) = predicate {
                    callback(v);
                }
                lookup_term_pattern_variables(object, callback);
                if let Some(NamedNodePattern::Variable(v)) = graph_name {
                    callback(v);
                }
            }
            Self::Path {
                subject,
                object,
                graph_name,
                ..
            } => {
                lookup_term_pattern_variables(subject, callback);
                lookup_term_pattern_variables(object, callback);
                if let Some(NamedNodePattern::Variable(v)) = graph_name {
                    callback(v);
                }
            }
            Self::Graph { graph_name } => {
                if let NamedNodePattern::Variable(v) = graph_name {
                    callback(v);
                }
            }
            Self::Filter { inner, expression } => {
                expression.lookup_used_variables(callback);
                inner.lookup_used_variables(callback);
            }
            Self::Union { inner } => {
                for child in inner {
                    child.lookup_used_variables(callback);
                }
            }
            Self::Join { left, right, .. } | Self::Minus { left, right, .. } => {
                left.lookup_used_variables(callback);
                right.lookup_used_variables(callback);
            }
            #[cfg(feature = "sep-0006")]
            Self::Lateral { left, right } => {
                left.lookup_used_variables(callback);
                right.lookup_used_variables(callback);
            }
            Self::LeftJoin {
                left,
                right,
                expression,
                ..
            } => {
                expression.lookup_used_variables(callback);
                left.lookup_used_variables(callback);
                right.lookup_used_variables(callback);
            }
            Self::Extend {
                inner,
                variable,
                expression,
            } => {
                callback(variable);
                expression.lookup_used_variables(callback);
                inner.lookup_used_variables(callback);
            }
            Self::OrderBy { inner, .. }
            | Self::Distinct { inner }
            | Self::Reduced { inner }
            | Self::Slice { inner, .. } => inner.lookup_used_variables(callback),
            Self::Service { inner, name, .. } => {
                if let NamedNodePattern::Variable(v) = name {
                    callback(v);
                }
                inner.lookup_used_variables(callback);
            }
            Self::Group {
                variables,
                aggregates,
                ..
            } => {
                for v in variables {
                    callback(v);
                }
                for (v, _) in aggregates {
                    callback(v);
                }
            }
        }
    }

    fn from_sparql_algebra(
        pattern: &AlGraphPattern,
        graph_name: Option<&NamedNodePattern>,
        blank_nodes: &mut HashMap<BlankNode, Variable>,
    ) -> Self {
        match pattern {
            AlGraphPattern::Bgp { patterns } => patterns
                .iter()
                .map(|p| {
                    let (subject, predicate, object) =
                        Self::triple_pattern_from_algebra(p, blank_nodes);
                    Self::QuadPattern {
                        subject,
                        predicate,
                        object,
                        graph_name: graph_name.cloned(),
                    }
                })
                .reduce(|a, b| Self::Join {
                    left: Box::new(a),
                    right: Box::new(b),
                    algorithm: JoinAlgorithm::default(),
                })
                .unwrap_or_else(|| {
                    if let Some(graph_name) = graph_name {
                        Self::Graph {
                            graph_name: graph_name.clone(),
                        }
                    } else {
                        Self::empty_singleton()
                    }
                }),
            AlGraphPattern::Path {
                subject,
                path,
                object,
            } => Self::Path {
                subject: Self::term_pattern_from_algebra(subject, blank_nodes),
                path: path.clone(),
                object: Self::term_pattern_from_algebra(object, blank_nodes),
                graph_name: graph_name.cloned(),
            },
            AlGraphPattern::Join { left, right } => Self::Join {
                left: Box::new(Self::from_sparql_algebra(left, graph_name, blank_nodes)),
                right: Box::new(Self::from_sparql_algebra(right, graph_name, blank_nodes)),
                algorithm: JoinAlgorithm::default(),
            },
            AlGraphPattern::LeftJoin {
                left,
                right,
                expression,
            } => Self::LeftJoin {
                left: Box::new(Self::from_sparql_algebra(left, graph_name, blank_nodes)),
                right: Box::new(Self::from_sparql_algebra(right, graph_name, blank_nodes)),
                expression: expression.as_ref().map_or_else(
                    || true.into(),
                    |e| Expression::from_sparql_algebra(e, graph_name),
                ),
                algorithm: LeftJoinAlgorithm::default(),
            },
            #[cfg(feature = "sep-0006")]
            AlGraphPattern::Lateral { left, right } => Self::Lateral {
                left: Box::new(Self::from_sparql_algebra(left, graph_name, blank_nodes)),
                right: Box::new(Self::from_sparql_algebra(right, graph_name, blank_nodes)),
            },
            AlGraphPattern::Filter { inner, expr } => Self::Filter {
                inner: Box::new(Self::from_sparql_algebra(inner, graph_name, blank_nodes)),
                expression: Expression::from_sparql_algebra(expr, graph_name),
            },
            AlGraphPattern::Union { left, right } => Self::Union {
                inner: vec![
                    Self::from_sparql_algebra(left, graph_name, blank_nodes),
                    Self::from_sparql_algebra(right, graph_name, blank_nodes),
                ],
            },
            AlGraphPattern::Graph { inner, name } => {
                let mut inner_pattern =
                    Self::from_sparql_algebra(inner, Some(name), blank_nodes);
                if let NamedNodePattern::Variable(graph_variable) = name
                    && (contains_left_join(inner)
                        || graph_variable_used_inside(inner, graph_variable, &inner_pattern))
                {
                    let local_graph_variable = fresh_variable_not_in_pattern(&inner_pattern, &[]);
                    rename_graph_position_variable(
                        &mut inner_pattern,
                        graph_variable,
                        &local_graph_variable,
                    );
                    let graph_check = Self::Graph {
                        graph_name: name.clone(),
                    };
                    #[cfg(feature = "sep-0006")]
                    let graph_join = if matches!(inner.as_ref(), AlGraphPattern::Project { .. }) {
                        Self::lateral(graph_check, inner_pattern)
                    } else {
                        Self::join(graph_check, inner_pattern, JoinAlgorithm::default())
                    };
                    #[cfg(not(feature = "sep-0006"))]
                    let graph_join =
                        Self::join(graph_check, inner_pattern, JoinAlgorithm::default());
                    let constrained = Self::filter(
                        graph_join,
                        Expression::Equal(
                            Box::new(Expression::Variable(graph_variable.clone())),
                            Box::new(Expression::Variable(local_graph_variable.clone())),
                        ),
                    );
                    let mut projected_variables = Vec::new();
                    constrained.lookup_used_variables(&mut |variable| {
                        if variable != &local_graph_variable
                            && !projected_variables.contains(variable)
                        {
                            projected_variables.push(variable.clone());
                        }
                    });
                    Self::project(constrained, projected_variables)
                } else {
                    #[cfg(feature = "sep-0006")]
                    if matches!(inner.as_ref(), AlGraphPattern::Project { .. }) {
                        return Self::lateral(
                            Self::Graph {
                                graph_name: name.clone(),
                            },
                            inner_pattern,
                        );
                    }
                    inner_pattern
                }
            }
            AlGraphPattern::Extend {
                inner,
                expression,
                variable,
            } => Self::Extend {
                inner: Box::new(Self::from_sparql_algebra(inner, graph_name, blank_nodes)),
                expression: Expression::from_sparql_algebra(expression, graph_name),
                variable: variable.clone(),
            },
            AlGraphPattern::Minus { left, right } => Self::Minus {
                left: Box::new({
                    let left = Self::from_sparql_algebra(left, graph_name, blank_nodes);
                    if let Some(NamedNodePattern::Variable(graph_variable)) = graph_name {
                        let mut variables = Vec::new();
                        left.lookup_used_variables(&mut |variable| {
                            if variable != graph_variable && !variables.contains(variable) {
                                variables.push(variable.clone());
                            }
                        });
                        Self::project(left, variables)
                    } else {
                        left
                    }
                }),
                right: Box::new({
                    let right = Self::from_sparql_algebra(right, graph_name, blank_nodes);
                    if let Some(NamedNodePattern::Variable(graph_variable)) = graph_name {
                        let mut variables = Vec::new();
                        right.lookup_used_variables(&mut |variable| {
                            if variable != graph_variable && !variables.contains(variable) {
                                variables.push(variable.clone());
                            }
                        });
                        Self::project(right, variables)
                    } else {
                        right
                    }
                }),
                algorithm: MinusAlgorithm::default(),
            },
            AlGraphPattern::Values {
                variables,
                bindings,
            } => {
                let values = Self::Values {
                    variables: variables.clone(),
                    bindings: bindings.clone(),
                };
                if let Some(graph_name) = graph_name {
                    Self::join(
                        Self::Graph {
                            graph_name: graph_name.clone(),
                        },
                        values,
                        JoinAlgorithm::default(),
                    )
                } else {
                    values
                }
            }
            AlGraphPattern::OrderBy { inner, expression } => {
                let mut inner = Self::from_sparql_algebra(inner, graph_name, blank_nodes);
                let mut expressions = Vec::with_capacity(expression.len());
                for e in expression {
                    expressions.push(match e {
                        AlOrderExpression::Asc(e) => {
                            let v;
                            (v, inner) = Self::algebra_expression_to_constant_or_variable(
                                e, inner, graph_name,
                            );
                            OrderExpression::Asc(Expression::Variable(v))
                        }
                        AlOrderExpression::Desc(e) => {
                            let v;
                            (v, inner) = Self::algebra_expression_to_constant_or_variable(
                                e, inner, graph_name,
                            );
                            OrderExpression::Desc(Expression::Variable(v))
                        }
                    });
                }
                Self::OrderBy {
                    inner: Box::new(inner),
                    expression: expressions,
                }
            }
            AlGraphPattern::Project { inner, variables } => {
                let mut projected_variables = variables.clone();
                let mut inner = Self::from_sparql_algebra(inner, graph_name, &mut HashMap::new());
                if let Some(NamedNodePattern::Variable(graph_variable)) = graph_name {
                    if !projected_variables.contains(graph_variable) {
                        let local_graph_variable =
                            fresh_variable_not_in_pattern(&inner, &projected_variables);
                        rename_variable_in_non_graph_positions(
                            &mut inner,
                            graph_variable,
                            &local_graph_variable,
                        );
                        projected_variables.push(graph_variable.clone());
                    }
                }
                Self::Project {
                    inner: Box::new(inner),
                    variables: projected_variables,
                }
            }
            AlGraphPattern::Distinct { inner } => Self::Distinct {
                inner: Box::new(Self::from_sparql_algebra(inner, graph_name, blank_nodes)),
            },
            AlGraphPattern::Reduced { inner } => Self::Distinct {
                inner: Box::new(Self::from_sparql_algebra(inner, graph_name, blank_nodes)),
            },
            AlGraphPattern::Slice {
                inner,
                start,
                length,
            } => Self::Slice {
                inner: Box::new(Self::from_sparql_algebra(inner, graph_name, blank_nodes)),
                start: *start,
                length: *length,
            },
            AlGraphPattern::Group {
                inner,
                variables,
                aggregates,
            } => Self::Group {
                inner: Box::new(Self::from_sparql_algebra(inner, graph_name, blank_nodes)),
                variables: variables.clone(),
                aggregates: aggregates
                    .iter()
                    .map(|(var, expr)| {
                        (
                            var.clone(),
                            AggregateExpression::from_sparql_algebra(expr, graph_name),
                        )
                    })
                    .collect(),
            },
            AlGraphPattern::Service {
                inner,
                name,
                silent,
            } => Self::Service {
                inner: Box::new(Self::from_sparql_algebra(inner, graph_name, blank_nodes)),
                name: name.clone(),
                silent: *silent,
            },
        }
    }

    fn triple_pattern_from_algebra(
        pattern: &TriplePattern,
        blank_nodes: &mut HashMap<BlankNode, Variable>,
    ) -> (GroundTermPattern, NamedNodePattern, GroundTermPattern) {
        (
            Self::term_pattern_from_algebra(&pattern.subject, blank_nodes),
            pattern.predicate.clone(),
            Self::term_pattern_from_algebra(&pattern.object, blank_nodes),
        )
    }

    fn term_pattern_from_algebra(
        pattern: &TermPattern,
        blank_nodes: &mut HashMap<BlankNode, Variable>,
    ) -> GroundTermPattern {
        match pattern {
            TermPattern::NamedNode(node) => node.clone().into(),
            TermPattern::BlankNode(node) => blank_nodes
                .entry(node.clone())
                .or_insert_with(new_var)
                .clone()
                .into(),
            TermPattern::Literal(literal) => literal.clone().into(),
            #[cfg(feature = "sparql-12")]
            TermPattern::Triple(pattern) => {
                let (subject, predicate, object) =
                    Self::triple_pattern_from_algebra(pattern, blank_nodes);
                GroundTriplePattern {
                    subject,
                    predicate,
                    object,
                }
                .into()
            }
            TermPattern::Variable(variable) => variable.clone().into(),
        }
    }

    /// Makes sure the expression is a variable, use Extend in the other cases
    fn algebra_expression_to_constant_or_variable(
        expression: &AlExpression,
        graph_pattern: GraphPattern,
        graph_name: Option<&NamedNodePattern>,
    ) -> (Variable, GraphPattern) {
        if let AlExpression::Variable(variable) = expression {
            (variable.clone(), graph_pattern)
        } else {
            let variable = Variable::new_unchecked(format!("{:x}", random::<u128>()));
            (
                variable.clone(),
                GraphPattern::Extend {
                    inner: Box::new(graph_pattern),
                    variable,
                    expression: Expression::from_sparql_algebra(expression, graph_name),
                },
            )
        }
    }
}

impl From<&AlGraphPattern> for GraphPattern {
    fn from(pattern: &AlGraphPattern) -> Self {
        Self::from_sparql_algebra(pattern, None, &mut HashMap::new())
    }
}

impl From<&GraphPattern> for AlGraphPattern {
    fn from(pattern: &GraphPattern) -> Self {
        match pattern {
            GraphPattern::QuadPattern {
                subject,
                predicate,
                object,
                graph_name,
            } => {
                let pattern = Self::Bgp {
                    patterns: vec![TriplePattern {
                        subject: subject.clone().into(),
                        predicate: predicate.clone(),
                        object: object.clone().into(),
                    }],
                };
                if let Some(graph_name) = graph_name {
                    Self::Graph {
                        inner: Box::new(pattern),
                        name: graph_name.clone(),
                    }
                } else {
                    pattern
                }
            }
            GraphPattern::Path {
                subject,
                path,
                object,
                graph_name,
            } => {
                let pattern = Self::Path {
                    subject: subject.clone().into(),
                    path: path.clone(),
                    object: object.clone().into(),
                };
                if let Some(graph_name) = graph_name {
                    Self::Graph {
                        inner: Box::new(pattern),
                        name: graph_name.clone(),
                    }
                } else {
                    pattern
                }
            }
            GraphPattern::Graph { graph_name } => Self::Graph {
                inner: Box::new(AlGraphPattern::Bgp {
                    patterns: Vec::new(),
                }),
                name: graph_name.clone(),
            },
            GraphPattern::Join { left, right, .. } => {
                match (left.as_ref().into(), right.as_ref().into()) {
                    (Self::Bgp { patterns: mut left }, Self::Bgp { patterns: right }) => {
                        left.extend(right);
                        Self::Bgp { patterns: left }
                    }
                    (left, right) => Self::Join {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
            GraphPattern::LeftJoin {
                left,
                right,
                expression,
                ..
            } => {
                let empty_expr = if let Expression::Literal(l) = expression {
                    l.datatype() == xsd::BOOLEAN && l.value() == "true"
                } else {
                    false
                };
                Self::LeftJoin {
                    left: Box::new(left.as_ref().into()),
                    right: Box::new(right.as_ref().into()),
                    expression: if empty_expr {
                        None
                    } else {
                        Some(expression.into())
                    },
                }
            }
            #[cfg(feature = "sep-0006")]
            GraphPattern::Lateral { left, right } => {
                match (left.as_ref().into(), right.as_ref().into()) {
                    (Self::Bgp { patterns: mut left }, Self::Bgp { patterns: right }) => {
                        left.extend(right);
                        Self::Bgp { patterns: left }
                    }
                    (left, right) => Self::Lateral {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                }
            }
            GraphPattern::Filter { inner, expression } => Self::Filter {
                inner: Box::new(inner.as_ref().into()),
                expr: expression.into(),
            },
            GraphPattern::Union { inner } => inner
                .iter()
                .map(Into::into)
                .reduce(|a, b| Self::Union {
                    left: Box::new(a),
                    right: Box::new(b),
                })
                .unwrap_or_else(|| Self::Values {
                    variables: Vec::new(),
                    bindings: Vec::new(),
                }),
            GraphPattern::Extend {
                inner,
                expression,
                variable,
            } => Self::Extend {
                inner: Box::new(inner.as_ref().into()),
                expression: expression.into(),
                variable: variable.clone(),
            },
            GraphPattern::Minus { left, right, .. } => Self::Minus {
                left: Box::new(left.as_ref().into()),
                right: Box::new(right.as_ref().into()),
            },
            GraphPattern::Values {
                variables,
                bindings,
            } => Self::Values {
                variables: variables.clone(),
                bindings: bindings.clone(),
            },
            GraphPattern::OrderBy { inner, expression } => Self::OrderBy {
                inner: Box::new(inner.as_ref().into()),
                expression: expression.iter().map(Into::into).collect(),
            },
            GraphPattern::Project { inner, variables } => Self::Project {
                inner: Box::new(inner.as_ref().into()),
                variables: variables.clone(),
            },
            GraphPattern::Distinct { inner } => Self::Distinct {
                inner: Box::new(inner.as_ref().into()),
            },
            GraphPattern::Reduced { inner } => Self::Distinct {
                inner: Box::new(inner.as_ref().into()),
            },
            GraphPattern::Slice {
                inner,
                start,
                length,
            } => Self::Slice {
                inner: Box::new(inner.as_ref().into()),
                start: *start,
                length: *length,
            },
            GraphPattern::Group {
                inner,
                variables,
                aggregates,
            } => Self::Group {
                inner: Box::new(inner.as_ref().into()),
                variables: variables.clone(),
                aggregates: aggregates
                    .iter()
                    .map(|(var, expr)| (var.clone(), expr.into()))
                    .collect(),
            },
            GraphPattern::Service {
                inner,
                name,
                silent,
            } => Self::Service {
                inner: Box::new(inner.as_ref().into()),
                name: name.clone(),
                silent: *silent,
            },
        }
    }
}

/// The join algorithm used (c.f. [`GraphPattern::Join`]).
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub enum JoinAlgorithm {
    HashBuildLeftProbeRight { keys: Vec<Variable> },
}

impl Default for JoinAlgorithm {
    fn default() -> Self {
        Self::HashBuildLeftProbeRight {
            keys: Vec::default(),
        }
    }
}

/// The left join algorithm used (c.f. [`GraphPattern::LeftJoin`]).
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub enum LeftJoinAlgorithm {
    HashBuildRightProbeLeft { keys: Vec<Variable> },
}

impl Default for LeftJoinAlgorithm {
    fn default() -> Self {
        Self::HashBuildRightProbeLeft {
            keys: Vec::default(),
        }
    }
}

/// The left join algorithm used (c.f. [`GraphPattern::Minus`]).
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub enum MinusAlgorithm {
    HashBuildRightProbeLeft { keys: Vec<Variable> },
}

impl Default for MinusAlgorithm {
    fn default() -> Self {
        Self::HashBuildRightProbeLeft {
            keys: Vec::default(),
        }
    }
}

/// A set function used in aggregates (c.f. [`GraphPattern::Group`]).
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub enum AggregateExpression {
    CountSolutions {
        distinct: bool,
    },
    FunctionCall {
        name: AggregateFunction,
        expr: Expression,
        distinct: bool,
    },
}

impl AggregateExpression {
    fn from_sparql_algebra(
        expression: &AlAggregateExpression,
        graph_name: Option<&NamedNodePattern>,
    ) -> Self {
        match expression {
            AlAggregateExpression::CountSolutions { distinct } => Self::CountSolutions {
                distinct: *distinct,
            },
            AlAggregateExpression::FunctionCall {
                name,
                expr,
                distinct,
            } => Self::FunctionCall {
                name: name.clone(),
                expr: Expression::from_sparql_algebra(expr, graph_name),
                distinct: *distinct,
            },
        }
    }
}

impl From<&AggregateExpression> for AlAggregateExpression {
    fn from(expression: &AggregateExpression) -> Self {
        match expression {
            AggregateExpression::CountSolutions { distinct } => Self::CountSolutions {
                distinct: *distinct,
            },
            AggregateExpression::FunctionCall {
                name,
                expr,
                distinct,
            } => Self::FunctionCall {
                name: name.clone(),
                expr: expr.into(),
                distinct: *distinct,
            },
        }
    }
}

/// An ordering comparator used by [`GraphPattern::OrderBy`].
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub enum OrderExpression {
    /// Ascending order
    Asc(Expression),
    /// Descending order
    Desc(Expression),
}

impl From<&OrderExpression> for AlOrderExpression {
    fn from(expression: &OrderExpression) -> Self {
        match expression {
            OrderExpression::Asc(e) => Self::Asc(e.into()),
            OrderExpression::Desc(e) => Self::Desc(e.into()),
        }
    }
}

fn new_var() -> Variable {
    Variable::new_unchecked(format!("{:x}", random::<u128>()))
}

fn contains_left_join(pattern: &AlGraphPattern) -> bool {
    match pattern {
        AlGraphPattern::LeftJoin { .. } => true,
        AlGraphPattern::Join { left, right }
        | AlGraphPattern::Union { left, right }
        | AlGraphPattern::Minus { left, right } => {
            contains_left_join(left) || contains_left_join(right)
        }
        #[cfg(feature = "sep-0006")]
        AlGraphPattern::Lateral { left, right } => {
            contains_left_join(left) || contains_left_join(right)
        }
        AlGraphPattern::Graph { inner, .. }
        | AlGraphPattern::Filter { inner, .. }
        | AlGraphPattern::Extend { inner, .. }
        | AlGraphPattern::OrderBy { inner, .. }
        | AlGraphPattern::Project { inner, .. }
        | AlGraphPattern::Distinct { inner }
        | AlGraphPattern::Reduced { inner }
        | AlGraphPattern::Slice { inner, .. }
        | AlGraphPattern::Group { inner, .. }
        | AlGraphPattern::Service { inner, .. } => contains_left_join(inner),
        AlGraphPattern::Bgp { .. }
        | AlGraphPattern::Path { .. }
        | AlGraphPattern::Values { .. } => false,
    }
}

fn fresh_variable_not_in_pattern(
    pattern: &GraphPattern,
    projected_variables: &[Variable],
) -> Variable {
    let mut used = HashSet::new();
    pattern.lookup_used_variables(&mut |v| {
        used.insert(v.clone());
    });
    used.extend(projected_variables.iter().cloned());
    loop {
        let candidate = new_var();
        if !used.contains(&candidate) {
            return candidate;
        }
    }
}

fn rename_named_node_pattern_variable(
    pattern: &mut NamedNodePattern,
    from: &Variable,
    to: &Variable,
) {
    if let NamedNodePattern::Variable(variable) = pattern {
        if variable == from {
            *variable = to.clone();
        }
    }
}

fn rename_ground_term_pattern_variable(
    pattern: &mut GroundTermPattern,
    from: &Variable,
    to: &Variable,
) {
    if let GroundTermPattern::Variable(variable) = pattern {
        if variable == from {
            *variable = to.clone();
        }
    }
    #[cfg(feature = "sparql-12")]
    if let GroundTermPattern::Triple(triple) = pattern {
        rename_ground_term_pattern_variable(&mut triple.subject, from, to);
        rename_named_node_pattern_variable(&mut triple.predicate, from, to);
        rename_ground_term_pattern_variable(&mut triple.object, from, to);
    }
}

fn rename_expression_variable(expression: &mut Expression, from: &Variable, to: &Variable) {
    match expression {
        Expression::NamedNode(_) | Expression::Literal(_) => {}
        Expression::Variable(variable) | Expression::Bound(variable) => {
            if variable == from {
                *variable = to.clone();
            }
        }
        Expression::Or(inner)
        | Expression::And(inner)
        | Expression::Coalesce(inner)
        | Expression::FunctionCall(_, inner) => {
            for child in inner {
                rename_expression_variable(child, from, to);
            }
        }
        Expression::Equal(left, right)
        | Expression::SameTerm(left, right)
        | Expression::Greater(left, right)
        | Expression::GreaterOrEqual(left, right)
        | Expression::Less(left, right)
        | Expression::LessOrEqual(left, right)
        | Expression::Add(left, right)
        | Expression::Subtract(left, right)
        | Expression::Multiply(left, right)
        | Expression::Divide(left, right) => {
            rename_expression_variable(left, from, to);
            rename_expression_variable(right, from, to);
        }
        Expression::UnaryPlus(inner) | Expression::UnaryMinus(inner) | Expression::Not(inner) => {
            rename_expression_variable(inner, from, to)
        }
        Expression::Exists(pattern) => rename_variable_in_non_graph_positions(pattern, from, to),
        Expression::If(cond, then_branch, else_branch) => {
            rename_expression_variable(cond, from, to);
            rename_expression_variable(then_branch, from, to);
            rename_expression_variable(else_branch, from, to);
        }
    }
}

fn rename_aggregate_expression_variable(
    aggregate: &mut AggregateExpression,
    from: &Variable,
    to: &Variable,
) {
    if let AggregateExpression::FunctionCall { expr, .. } = aggregate {
        rename_expression_variable(expr, from, to);
    }
}

fn rename_order_expression_variable(order: &mut OrderExpression, from: &Variable, to: &Variable) {
    match order {
        OrderExpression::Asc(expression) | OrderExpression::Desc(expression) => {
            rename_expression_variable(expression, from, to);
        }
    }
}

/// Whether `graph_variable` is used inside `inner` for anything other than the graph name
/// that `GRAPH ?g { ... }` binds.
///
/// Only then does the group need the variable-scoping rewrite: SPARQL keeps `?g` out of
/// scope inside the group, so a `?g` written there is a distinct, initially unbound
/// variable that the outer graph name has to be joined against.
///
/// Looking for `?g` in the lowered pattern directly cannot answer this, because lowering
/// threads the graph name through the group itself — into quad and path graph positions,
/// and into sub-select projection lists. Lowering a second time under a fresh graph
/// variable removes that ambiguity: anything still naming `?g` is a real use.
fn graph_variable_used_inside(
    inner: &AlGraphPattern,
    graph_variable: &Variable,
    lowered: &GraphPattern,
) -> bool {
    let probe_graph_name = NamedNodePattern::Variable(fresh_variable_not_in_pattern(
        lowered,
        slice::from_ref(graph_variable),
    ));
    let probed =
        GraphPattern::from_sparql_algebra(inner, Some(&probe_graph_name), &mut HashMap::new());
    let mut used = false;
    probed.lookup_used_variables(&mut |variable| {
        if variable == graph_variable {
            used = true;
        }
    });
    used
}

fn rename_variable_in_non_graph_positions(
    pattern: &mut GraphPattern,
    from: &Variable,
    to: &Variable,
) {
    match pattern {
        GraphPattern::QuadPattern {
            subject,
            predicate,
            object,
            ..
        } => {
            rename_ground_term_pattern_variable(subject, from, to);
            rename_named_node_pattern_variable(predicate, from, to);
            rename_ground_term_pattern_variable(object, from, to);
        }
        GraphPattern::Path {
            subject, object, ..
        } => {
            rename_ground_term_pattern_variable(subject, from, to);
            rename_ground_term_pattern_variable(object, from, to);
        }
        GraphPattern::Graph { .. } => {}
        GraphPattern::Join { left, right, .. } | GraphPattern::Minus { left, right, .. } => {
            rename_variable_in_non_graph_positions(left, from, to);
            rename_variable_in_non_graph_positions(right, from, to);
        }
        #[cfg(feature = "sep-0006")]
        GraphPattern::Lateral { left, right } => {
            rename_variable_in_non_graph_positions(left, from, to);
            rename_variable_in_non_graph_positions(right, from, to);
        }
        GraphPattern::LeftJoin {
            left,
            right,
            expression,
            ..
        } => {
            rename_variable_in_non_graph_positions(left, from, to);
            rename_variable_in_non_graph_positions(right, from, to);
            rename_expression_variable(expression, from, to);
        }
        GraphPattern::Filter { expression, inner } => {
            rename_expression_variable(expression, from, to);
            rename_variable_in_non_graph_positions(inner, from, to);
        }
        GraphPattern::Union { inner } => {
            for child in inner {
                rename_variable_in_non_graph_positions(child, from, to);
            }
        }
        GraphPattern::Extend {
            inner,
            variable,
            expression,
        } => {
            rename_variable_in_non_graph_positions(inner, from, to);
            if variable == from {
                *variable = to.clone();
            }
            rename_expression_variable(expression, from, to);
        }
        GraphPattern::Values { variables, .. } => {
            for variable in variables {
                if variable == from {
                    *variable = to.clone();
                }
            }
        }
        GraphPattern::Project { inner, variables } => {
            for variable in variables {
                if variable == from {
                    *variable = to.clone();
                }
            }
            rename_variable_in_non_graph_positions(inner, from, to);
        }
        GraphPattern::OrderBy { inner, expression } => {
            rename_variable_in_non_graph_positions(inner, from, to);
            for order in expression {
                rename_order_expression_variable(order, from, to);
            }
        }
        GraphPattern::Distinct { inner }
        | GraphPattern::Reduced { inner }
        | GraphPattern::Slice { inner, .. } => {
            rename_variable_in_non_graph_positions(inner, from, to);
        }
        GraphPattern::Group {
            inner,
            variables,
            aggregates,
        } => {
            rename_variable_in_non_graph_positions(inner, from, to);
            for variable in variables {
                if variable == from {
                    *variable = to.clone();
                }
            }
            for (variable, aggregate) in aggregates {
                if variable == from {
                    *variable = to.clone();
                }
                rename_aggregate_expression_variable(aggregate, from, to);
            }
        }
        GraphPattern::Service { name, inner, .. } => {
            rename_named_node_pattern_variable(name, from, to);
            rename_variable_in_non_graph_positions(inner, from, to);
        }
    }
}

fn rename_graph_position_variable(pattern: &mut GraphPattern, from: &Variable, to: &Variable) {
    match pattern {
        GraphPattern::QuadPattern { graph_name, .. } | GraphPattern::Path { graph_name, .. } => {
            if let Some(NamedNodePattern::Variable(variable)) = graph_name
                && variable == from
            {
                *variable = to.clone();
            }
        }
        GraphPattern::Graph { graph_name } => {
            if let NamedNodePattern::Variable(variable) = graph_name
                && variable == from
            {
                *variable = to.clone();
            }
        }
        GraphPattern::Join { left, right, .. } | GraphPattern::Minus { left, right, .. } => {
            rename_graph_position_variable(left, from, to);
            rename_graph_position_variable(right, from, to);
        }
        #[cfg(feature = "sep-0006")]
        GraphPattern::Lateral { left, right } => {
            rename_graph_position_variable(left, from, to);
            rename_graph_position_variable(right, from, to);
        }
        GraphPattern::LeftJoin { left, right, .. } => {
            rename_graph_position_variable(left, from, to);
            rename_graph_position_variable(right, from, to);
        }
        GraphPattern::Filter { inner, .. }
        | GraphPattern::Distinct { inner }
        | GraphPattern::Reduced { inner }
        | GraphPattern::Slice { inner, .. }
        | GraphPattern::Service { inner, .. } => rename_graph_position_variable(inner, from, to),
        GraphPattern::Union { inner } => {
            for child in inner {
                rename_graph_position_variable(child, from, to);
            }
        }
        GraphPattern::Extend { inner, .. }
        | GraphPattern::Project { inner, .. }
        | GraphPattern::OrderBy { inner, .. }
        | GraphPattern::Group { inner, .. } => rename_graph_position_variable(inner, from, to),
        GraphPattern::Values { .. } => {}
    }
}

fn order_pair<T: Hash>(a: T, b: T) -> (T, T) {
    if hash(&a) <= hash(&b) { (a, b) } else { (b, a) }
}

fn order_vec<T: Hash>(mut vec: Vec<T>) -> Vec<T> {
    vec.sort_unstable_by_key(|a| hash(a));
    vec
}

fn hash(v: impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    v.hash(&mut hasher);
    hasher.finish()
}

fn lookup_term_pattern_variables<'a>(
    pattern: &'a GroundTermPattern,
    callback: &mut impl FnMut(&'a Variable),
) {
    if let GroundTermPattern::Variable(v) = pattern {
        callback(v);
    }
    #[cfg(feature = "sparql-12")]
    if let GroundTermPattern::Triple(t) = pattern {
        lookup_term_pattern_variables(&t.subject, callback);
        if let NamedNodePattern::Variable(v) = &t.predicate {
            callback(v);
        }
        lookup_term_pattern_variables(&t.object, callback);
    }
}
