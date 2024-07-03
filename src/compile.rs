//! Compile the parsed ast into a simplicity program

use std::collections::HashMap;
use std::str::FromStr;

use simplicity::node::{CoreConstructible as _, JetConstructible as _};
use simplicity::{jet::Elements, Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::num::NonZeroPow2Usize;
use crate::parse::{Identifier, Match, Pattern, SingleExpressionInner, Span};
use crate::pattern::BasePattern;
use crate::types::AliasedType;
use crate::value::{StructuralValue, UIntValue};
use crate::{
    error::{Error, RichError, WithSpan},
    named::{ConstructExt, ProgExt},
    parse::{Call, CallName, Expression, ExpressionInner, Program, Statement},
    types::{ResolvedType, StructuralType, TypeInner, UIntType},
    ProgNode,
};

/// Each Simfony expression expects an _input value_.
/// A Simfony expression is translated into a Simplicity expression
/// that similarly expects an _input value_.
///
/// Simfony variable names are translated into Simplicity expressions
/// that extract the seeked value from the _input value_.
///
/// Each (nested) block expression introduces a new scope.
/// Bindings from inner scopes overwrite bindings from outer scopes.
/// Bindings live as long as their scope.
#[derive(Debug, Clone)]
pub struct GlobalScope {
    /// For each scope, the set of assigned variables.
    ///
    /// A stack of scopes. Each scope is a stack of patterns.
    /// New patterns are pushed onto the top _(current, innermost)_ scope.
    ///
    /// ## Input pattern
    ///
    /// The stack of scopes corresponds to an _input pattern_.
    /// All valid input values match the input pattern.
    ///
    /// ## Example
    ///
    /// The stack `[[p1], [p2, p3]]` corresponds to a nested product pattern:
    ///
    /// ```text
    ///    .
    ///   / \
    /// p3   .
    ///     / \
    ///   p2   p1
    /// ```
    ///
    /// Inner scopes occur higher in the tree than outer scopes.
    /// Later assignments occur higher in the tree than earlier assignments.
    /// ```
    variables: Vec<Vec<Pattern>>,
    /// For each scope, the mapping of type aliases to resolved types.
    aliases: Vec<HashMap<Identifier, ResolvedType>>,
}

impl GlobalScope {
    /// Create a new [`GlobalScope`] for an `input` value that matches the pattern.
    pub fn new(input: Pattern) -> Self {
        GlobalScope {
            variables: vec![vec![input]],
            aliases: vec![HashMap::new()],
        }
    }

    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(Vec::new());
        self.aliases.push(HashMap::new());
    }

    /// Pop the current scope from the stack.
    ///
    /// # Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Empty stack");
        self.aliases.pop().expect("Empty stack");
    }

    /// Push an assignment to the current scope.
    ///
    /// Update the input pattern accordingly:
    ///
    /// ```text
    ///   .
    ///  / \
    /// p   previous
    /// ```
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert(&mut self, pattern: Pattern) {
        self.variables
            .last_mut()
            .expect("Empty stack")
            .push(pattern);
    }

    /// Resolve a type with aliases to a type without aliases.
    pub fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Identifier> {
        let get_alias = |name: &Identifier| -> Option<ResolvedType> {
            self.aliases
                .iter()
                .rev()
                .find_map(|scope| scope.get(name))
                .cloned()
        };
        ty.resolve(get_alias)
    }

    /// Push a type alias to the current scope.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert_alias(&mut self, name: Identifier, ty: AliasedType) -> Result<(), Identifier> {
        let resolved_ty = self.resolve(&ty)?;
        self.aliases
            .last_mut()
            .expect("Empty stack")
            .insert(name, resolved_ty);
        Ok(())
    }

    /// Get the input pattern.
    ///
    /// All valid input values match the input pattern.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    fn get_input_pattern(&self) -> Pattern {
        let mut it = self.variables.iter().flat_map(|scope| scope.iter());
        let first = it.next().expect("Empty stack");
        it.cloned()
            .fold(first.clone(), |acc, next| Pattern::product(next, acc))
    }

    /// Compute a Simplicity expression that takes a valid input value (that matches the input pattern)
    /// and that produces as output a value that matches the `target` pattern.
    ///
    /// ## Example
    ///
    /// ```
    /// let a: u8 = 0;
    /// let b = {
    ///     let b: u8 = 1;
    ///     let c: u8 = 2;
    ///     (a, b)  // here we seek the value of `(a, b)`
    /// };
    /// ```
    ///
    /// The input pattern looks like this:
    ///
    /// ```text
    ///   .
    ///  / \
    /// c   .
    ///    / \
    ///   b   .
    ///      / \
    ///     a   _
    /// ```
    ///
    /// The expression `drop (IOH & OH)` returns the seeked value.
    pub fn get(&self, target: &BasePattern) -> Option<ProgNode> {
        BasePattern::from(&self.get_input_pattern()).translate(target)
    }
}

fn eval_blk(
    stmts: &[Statement],
    scope: &mut GlobalScope,
    index: usize,
    last_expr: Option<&Expression>,
) -> Result<ProgNode, RichError> {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.eval(scope, None),
            None => Ok(ProgNode::unit()),
        };
    }
    match &stmts[index] {
        Statement::Assignment(assignment) => {
            let ty = scope
                .resolve(&assignment.ty)
                .map_err(Error::UndefinedAlias)
                .with_span(assignment.span)?;
            let expr = assignment.expression.eval(scope, Some(&ty))?;
            scope.insert(assignment.pattern.clone());
            let left = ProgNode::pair_iden(&expr);
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            ProgNode::comp(&left, &right).with_span(assignment.span)
        }
        Statement::Expression(expression) => {
            let left = expression.eval(scope, None)?;
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            combine_seq(&left, &right).with_span(expression)
        }
        Statement::TypeAlias(alias) => {
            scope
                .insert_alias(alias.name.clone(), alias.ty.clone())
                .map_err(Error::UndefinedAlias)
                .with_span(alias.span)?;
            eval_blk(stmts, scope, index + 1, last_expr)
        }
    }
}

fn combine_seq(a: &ProgNode, b: &ProgNode) -> Result<ProgNode, simplicity::types::Error> {
    let pair = ProgNode::pair(a, b)?;
    let drop_iden = ProgNode::drop_(&ProgNode::iden());
    ProgNode::comp(&pair, &drop_iden)
}

impl Program {
    pub fn eval(&self, scope: &mut GlobalScope) -> Result<ProgNode, RichError> {
        eval_blk(&self.statements, scope, 0, None)
    }
}

impl Call {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        _reqd_ty: Option<&ResolvedType>,
    ) -> Result<ProgNode, RichError> {
        match &self.name {
            CallName::Jet(name) => {
                let args = SingleExpressionInner::Tuple(self.args.clone());
                // TODO: Pass the jet source type here.
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                let args_expr = args.eval(scope, None, self.span)?;
                let jet = Elements::from_str(name.as_inner())
                    .map_err(|_| Error::JetDoesNotExist(name.clone()))
                    .with_span(self.span)?;
                let jet_expr = ProgNode::jet(jet);
                ProgNode::comp(&args_expr, &jet_expr).with_span(self.span)
            }
            CallName::UnwrapLeft => {
                debug_assert!(self.args.len() == 1);
                let b = self.args[0].eval(scope, None)?;
                let left_and_unit = ProgNode::pair_unit(&b);
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertl_take(&ProgNode::iden(), fail_cmr);
                ProgNode::comp(&left_and_unit, &get_inner).with_span(self.span)
            }
            CallName::UnwrapRight | CallName::Unwrap => {
                debug_assert!(self.args.len() == 1);
                let c = self.args[0].eval(scope, None)?;
                let right_and_unit = ProgNode::pair_unit(&c);
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertr_take(fail_cmr, &ProgNode::iden());
                ProgNode::comp(&right_and_unit, &get_inner).with_span(self.span)
            }
        }
    }
}

impl Expression {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&ResolvedType>,
    ) -> Result<ProgNode, RichError> {
        match &self.inner {
            ExpressionInner::Block(stmts, expr) => {
                scope.push_scope();
                let res = eval_blk(stmts, scope, 0, Some(expr.as_ref()));
                scope.pop_scope();
                res
            }
            ExpressionInner::Single(e) => e.inner.eval(scope, reqd_ty, self.span),
        }
    }
}

impl SingleExpressionInner {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&ResolvedType>,
        span: Span,
    ) -> Result<ProgNode, RichError> {
        let expr = match self {
            SingleExpressionInner::Left(l) => {
                let l = l.eval(scope, None)?;
                ProgNode::injl(&l)
            }
            SingleExpressionInner::Option(None) => ProgNode::_false(),
            SingleExpressionInner::Right(r) | SingleExpressionInner::Option(Some(r)) => {
                let r = r.eval(scope, None)?;
                ProgNode::injr(&r)
            }
            SingleExpressionInner::Boolean(false) => ProgNode::_false(),
            SingleExpressionInner::Boolean(true) => ProgNode::_true(),
            SingleExpressionInner::Decimal(decimal) => {
                let reqd_ty = reqd_ty
                    .cloned()
                    .unwrap_or(ResolvedType::from(UIntType::U32));
                let ty = UIntType::try_from(&reqd_ty)
                    .map_err(|_| Error::TypeValueMismatch(reqd_ty))
                    .with_span(span)?;
                let value = UIntValue::parse_decimal(decimal, ty).with_span(span)?;
                let value = StructuralValue::from(value);
                ProgNode::unit_comp(&ProgNode::const_word(value.into()))
            }
            SingleExpressionInner::BitString(bits) => {
                let value = StructuralValue::from(UIntValue::from(bits));
                ProgNode::unit_comp(&ProgNode::const_word(value.into()))
            }
            SingleExpressionInner::ByteString(bytes) => {
                let value = StructuralValue::from(UIntValue::from(bytes));
                ProgNode::unit_comp(&ProgNode::const_word(value.into()))
            }
            SingleExpressionInner::Witness(name) => ProgNode::witness(name.as_inner().clone()),
            SingleExpressionInner::Variable(identifier) => scope
                .get(&BasePattern::Identifier(identifier.clone()))
                .ok_or(Error::UndefinedVariable(identifier.clone()))
                .with_span(span)?,
            SingleExpressionInner::Call(call) => call.eval(scope, reqd_ty)?,
            SingleExpressionInner::Expression(expression) => expression.eval(scope, reqd_ty)?,
            SingleExpressionInner::Match(match_) => match_.eval(scope, reqd_ty)?,
            SingleExpressionInner::Tuple(elements) => {
                // Type checking is annoying when reqd_ty can be None
                // TODO: Type-check this code once reqd_ty is an explicit &ResolvedType
                let nodes: Vec<Result<ProgNode, RichError>> =
                    elements.iter().map(|e| e.eval(scope, None)).collect();
                let tree = BTreeSlice::from_slice(&nodes);
                tree.fold(|res_a, res_b| {
                    res_a.and_then(|a| res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(span)))
                })
                .unwrap_or_else(|| Ok(ProgNode::unit()))?
            }
            SingleExpressionInner::Array(elements) => {
                let el_type = match reqd_ty.map(ResolvedType::as_inner) {
                    Some(TypeInner::Array(el_type, size)) => {
                        if *size != elements.len() {
                            return Err(Error::TypeValueMismatch(reqd_ty.unwrap().clone()))
                                .with_span(span);
                        }
                        Some(el_type.as_ref())
                    }
                    _ => None,
                };
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                let nodes: Vec<Result<ProgNode, RichError>> =
                    elements.iter().map(|e| e.eval(scope, el_type)).collect();
                let tree = BTreeSlice::from_slice(&nodes);
                tree.fold(|res_a, res_b| {
                    res_a.and_then(|a| res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(span)))
                })
                .unwrap_or_else(|| Ok(ProgNode::unit()))?
            }
            SingleExpressionInner::List(elements) => {
                let el_type = match reqd_ty.map(ResolvedType::as_inner) {
                    Some(TypeInner::List(el_type, _)) => Some(el_type.as_ref()),
                    _ => None,
                };
                let nodes: Vec<Result<ProgNode, RichError>> =
                    elements.iter().map(|e| e.eval(scope, el_type)).collect();
                let bound = match reqd_ty.map(ResolvedType::as_inner) {
                    Some(TypeInner::List(_, bound)) => *bound,
                    _ => NonZeroPow2Usize::next(elements.len().saturating_add(1)),
                };
                if bound.get() <= nodes.len() {
                    return Err(Error::TypeValueMismatch(reqd_ty.unwrap().clone())).with_span(span);
                }
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                let partition = Partition::from_slice(&nodes, bound.get() / 2);
                let process =
                    |block: &[Result<ProgNode, RichError>]| -> Result<ProgNode, RichError> {
                        let tree = BTreeSlice::from_slice(block);
                        tree.fold(|res_a, res_b| {
                            res_a.and_then(|a| {
                                res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(span))
                            })
                        })
                        .map(|res| res.map(|array| ProgNode::injr(&array)))
                        .unwrap_or_else(|| Ok(ProgNode::_false()))
                    };

                partition.fold(process, |res_a, res_b| {
                    res_a.and_then(|a| res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(span)))
                })?
            }
        };
        if let Some(reqd_ty) = reqd_ty {
            expr.arrow()
                .target
                .unify(&StructuralType::from(reqd_ty).to_unfinalized(), "")
                .map_err(|e| Error::CannotCompile(e.to_string()))
                .with_span(span)?;
        }
        Ok(expr)
    }
}

impl Match {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&ResolvedType>,
    ) -> Result<ProgNode, RichError> {
        let mut l_scope = scope.clone();
        l_scope.insert(
            self.left()
                .pattern
                .get_identifier()
                .cloned()
                .map(Pattern::Identifier)
                .unwrap_or(Pattern::Ignore),
        );
        let l_compiled = self.left().expression.eval(&mut l_scope, reqd_ty)?;

        let mut r_scope = scope.clone();
        r_scope.insert(
            self.right()
                .pattern
                .get_identifier()
                .cloned()
                .map(Pattern::Identifier)
                .unwrap_or(Pattern::Ignore),
        );
        let r_compiled = self.right().expression.eval(&mut r_scope, reqd_ty)?;

        // TODO: Enforce target type A + B for m_expr
        let scrutinized_input = self.scrutinee().eval(scope, None)?;
        let input = ProgNode::pair_iden(&scrutinized_input);
        let output = ProgNode::case(&l_compiled, &r_compiled).with_span(self)?;
        ProgNode::comp(&input, &output).with_span(self)
    }
}
