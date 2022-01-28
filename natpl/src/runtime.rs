use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    syntax::{Expression, HasFC, InfixOp, Item, LineItem, Name, PrefixOp, SiPrefix, FC},
    value_unit::{Unit, Value, ValueKind, ValueKindNumberZipResult},
};

use fraction::{BigDecimal, ToPrimitive};
use thiserror::Error;

#[derive(Debug, Default, Clone)]
pub struct CallStack(Vec<HashMap<Name, Value>>);

impl CallStack {
    // Name might be changed in future
    #[allow(clippy::ptr_arg)]
    fn lookup(&self, name: &Name) -> Option<&Value> {
        self.0.iter().rev().find_map(|map| map.get(name))
    }

    fn push(&mut self, map: HashMap<Name, Value>) {
        self.0.push(map)
    }

    fn pop(&mut self) {
        let _ = self.0.pop();
    }
}

#[derive(Default, Clone)]
pub struct Runtime {
    units: HashSet<Name>,
    unit_aliases: HashMap<Name, Value>,
    conversions: HashMap<(Unit, Unit), (Name, Expression)>,
    /// Variables in the global scope
    variables: HashMap<Name, Value>,
    functions: HashMap<Name, (Vec<Name>, Expression)>,
}

impl Runtime {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn get_variable(&self, name: &str) -> Option<Value> {
        self.variables.get(name).cloned()
    }

    pub fn set_variable(&mut self, name: &str, value: Value) {
        let _ = self.variables.insert(name.to_string(), value);
    }

    pub fn eval_line_item(
        &mut self,
        item: LineItem,
        call_stack: &mut CallStack,
    ) -> Result<EvalResult, ItemError> {
        match self.line_item_to_item(item) {
            Some(item) => self.eval_item(item, call_stack),
            None => Ok(EvalResult::Empty),
        }
    }

    /// Given a unit, find other unit aliases with the same unit
    pub fn find_units<'a, 'b: 'a>(&'b self, unit: &'a Unit) -> HashMap<&'a Name, ValueKind> {
        self.unit_aliases
            .iter()
            .filter_map(|(name, val)| {
                if &val.unit == unit {
                    Some((name, val.kind.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn find_variables_with_unit<'a, 'b: 'a>(
        &'b self,
        unit: &'a Unit,
    ) -> HashMap<&'a Name, ValueKind> {
        self.variables
            .iter()
            .filter_map(|(name, val)| {
                if &val.unit == unit {
                    Some((name, val.kind.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    fn line_item_to_item(&mut self, item: LineItem) -> Option<Item> {
        let it = match item {
            LineItem::Empty => return None,
            LineItem::VarSearch(fc) => Item::VarSearch(fc),
            LineItem::UnitSearch(expr) => Item::UnitSearch(expr),
            LineItem::UnitDeclaration(fc, name) => Item::UnitDeclaration(fc, name),
            LineItem::UnitAlias(fc, name, expr) => Item::UnitAlias(fc, name, expr),
            LineItem::ConversionDeclaration {
                fc,
                name,
                unit_from,
                unit_to,
                body,
            } => Item::ConversionDeclaration {
                fc,
                name,
                unit_from,
                unit_to,
                body,
            },
            LineItem::Declaration(decl) => decl.into_declaration(),
            LineItem::PrintedExpression(fc, expr) => Item::PrintedExpression(fc, expr),
            LineItem::SilentExpression(expr) => Item::SilentExpression(expr),
        };
        Some(it)
    }

    fn eval_item(
        &mut self,
        item: Item,
        call_stack: &mut CallStack,
    ) -> Result<EvalResult, ItemError> {
        use std::collections::hash_map::Entry;

        match item {
            Item::VarSearch(_) => Ok(EvalResult::VariableSearchResult {
                unit_aliases: self
                    .unit_aliases
                    .iter()
                    .map(|(n, v)| (n.clone(), v.clone()))
                    .collect(),
                variables: self
                    .variables
                    .iter()
                    .map(|(n, v)| (n.clone(), v.clone()))
                    .collect(),
                functions: self
                    .functions
                    .iter()
                    .map(|(n, (args, _))| (n.clone(), args.clone()))
                    .collect(),
            }),
            Item::UnitSearch(expr) => {
                let val = self.eval_expr(&expr, call_stack)?;
                Ok(EvalResult::UnitSearchResult {
                    unit_aliases: self
                        .find_units(&val.unit)
                        .into_iter()
                        .map(|(n, v)| (n.clone(), v))
                        .collect(),
                    variables: self
                        .find_variables_with_unit(&val.unit)
                        .into_iter()
                        .map(|(n, v)| (n.clone(), v))
                        .collect(),
                    unit: val.unit,
                })
            }
            Item::UnitDeclaration(_, name) => {
                let name = name.name();

                let is_unique = self.units.insert(name.clone());
                if !is_unique {
                    Err(ItemError::UnitRedeclared(name))
                } else {
                    Ok(EvalResult::Empty)
                }
            }
            Item::UnitAlias(_, name, expr) => {
                let value = self.eval_expr(&expr, call_stack)?;

                let name = name.name();
                match self.unit_aliases.entry(name.clone()) {
                    Entry::Occupied(_) => Err(ItemError::UnitRedeclared(name)),
                    Entry::Vacant(entry) => {
                        let val = entry.insert(value).clone();
                        Ok(EvalResult::Value(val))
                    }
                }
            }
            Item::ConversionDeclaration {
                fc: _,
                name,
                unit_from,
                unit_to,
                body,
            } => {
                let from = self.eval_expr(&unit_from, &mut CallStack::default())?;
                let to = self.eval_expr(&unit_to, &mut CallStack::default())?;

                match self.conversions.entry((from.unit.clone(), to.unit.clone())) {
                    Entry::Occupied(_) => Err(ItemError::ConversionRedeclared {
                        from: from.unit,
                        to: to.unit,
                    }),
                    Entry::Vacant(entry) => {
                        let _ = entry.insert((name.name(), body));
                        Ok(EvalResult::Empty)
                    }
                }
            }
            Item::VariableDeclaration { fc: _, name, rhs } => {
                let name = name.name();
                let value = self.eval_expr(&rhs, call_stack)?;
                self.variables.insert(name, value.clone());
                Ok(EvalResult::Value(value))
            }
            Item::FunctionDeclaration {
                fc: _,
                name,
                arg_names,
                rhs,
            } => {
                let name = name.name();
                self.functions.insert(
                    name,
                    (arg_names.into_iter().map(|n| n.name()).collect(), rhs),
                );
                Ok(EvalResult::Empty)
            }
            Item::PrintedExpression(_, e) => {
                let val = self.eval_expr(&e, call_stack)?;
                Ok(EvalResult::PrintValue(e, val))
            }
            Item::SilentExpression(e) => {
                let val = self.eval_expr(&e, call_stack)?;
                Ok(EvalResult::Value(val))
            }
        }
    }

    fn eval_expr(&self, expr: &Expression, call_stack: &mut CallStack) -> Result<Value, EvalError> {
        match expr {
            Expression::IntegerLit { fc: _, val } => Ok(Value {
                kind: ValueKind::Number(val.clone()),
                unit: Unit::new(),
            }),
            Expression::FloatLit { fc: _, val } => Ok(Value {
                kind: ValueKind::Number(val.clone()),
                unit: Unit::new(),
            }),
            Expression::MaybeUnitPrefix {
                fc,
                name,
                full_name,
                prefix,
            } => {
                if let Some(val) = self.lookup(full_name, call_stack) {
                    return Ok(val);
                }

                if let Some(val) = self.lookup(name, call_stack) {
                    apply_prefix(*fc, *prefix, val)
                } else {
                    Err(EvalError::UndefinedName(*fc, full_name.clone()))
                }
            }
            Expression::Variable(id) => self
                .lookup(id.name_ref(), call_stack)
                .ok_or_else(|| EvalError::UndefinedName(id.fc(), id.name_ref().clone())),
            Expression::Call { fc, base, args } => {
                let base = self.eval_expr(&**base, call_stack)?;
                let args: Vec<_> = args
                    .iter()
                    .map(|e| Ok((e.fc(), self.eval_expr(e, call_stack)?)))
                    .collect::<Result<_, EvalError>>()?;

                match &base.kind {
                    ValueKind::FunctionRef(name) => {
                        if let Some(res) = crate::functions::builtin_func(*fc, name, &base, &args) {
                            res
                        } else if let Some((arg_names, body)) = self.functions.get(name) {
                            if args.len() != arg_names.len() {
                                return Err(EvalError::CallArgumentMismatch {
                                    fc: *fc,
                                    base: base.clone(),
                                    num_args_applied: args.len(),
                                    num_args_expected: arg_names.len(),
                                });
                            }
                            let arg_map = arg_names
                                .iter()
                                .zip(args)
                                .map(|(a, (_, v))| (a.clone(), v))
                                .collect();
                            call_stack.push(arg_map);

                            let res = self.eval_expr(body, call_stack);

                            call_stack.pop();

                            res
                        } else {
                            unreachable!()
                        }
                    }
                    _ => Err(EvalError::CallOnNonFunction(*fc, base.clone())),
                }
            }
            Expression::PrefixOp { fc, op, expr } => {
                let mut val = self.eval_expr(expr, call_stack)?;
                match op {
                    crate::syntax::PrefixOp::Pos => match &mut val.kind {
                        ValueKind::Number(_) => Ok(val),
                        ValueKind::FunctionRef(_) => {
                            Err(EvalError::InvalidPrefixOperator(*fc, *op, val))
                        }
                        ValueKind::Vector(_) => Ok(val),
                    },
                    crate::syntax::PrefixOp::Neg => {
                        fn negate(
                            fc: &FC,
                            op: &PrefixOp,
                            val: &Value,
                            val_kind: &ValueKind,
                        ) -> Result<ValueKind, EvalError> {
                            match val_kind {
                                ValueKind::Number(num) => Ok(ValueKind::Number(-&*num)),
                                ValueKind::FunctionRef(_) => {
                                    Err(EvalError::InvalidPrefixOperator(*fc, *op, val.clone()))
                                }
                                ValueKind::Vector(v) => {
                                    let vals = v
                                        .iter()
                                        .map(|vk| negate(fc, op, val, vk))
                                        .collect::<Result<_, _>>()?;
                                    Ok(ValueKind::Vector(vals))
                                }
                            }
                        }

                        Ok(Value {
                            kind: negate(fc, op, &val, &val.kind)?,
                            unit: val.unit,
                        })
                    }
                }
            }
            Expression::InfixOp { fc, op, lhs, rhs } => {
                self.eval_infix_op(*fc, *op, lhs, rhs, call_stack)
            }
            Expression::UnitOf(_, expr) => {
                let val = self.eval_expr(expr, call_stack)?;
                Ok(Value {
                    kind: ValueKind::Number(BigDecimal::from(1)),
                    unit: val.unit,
                })
            }
            Expression::Parenthesised(_, expr) => self.eval_expr(expr, call_stack),
            Expression::Vector(_, elems) => {
                let elems: Vec<_> = elems
                    .iter()
                    .map(|e| Ok((e.fc(), self.eval_expr(e, call_stack)?)))
                    .collect::<Result<_, EvalError>>()?;

                if elems.is_empty() {
                    Ok(Value {
                        kind: ValueKind::Vector(Vec::new()),
                        unit: Unit::new(),
                    })
                } else {
                    let mut iter = elems.iter();

                    let unit = iter.next().map(|(_, v)| v.unit.clone()).unwrap();
                    for (fc, elem) in iter {
                        if unit != elem.unit {
                            return Err(EvalError::UnitError(UnitError::UnitMismatch {
                                expected: unit,
                                found: elem.unit.clone(),
                                fc: *fc,
                            }));
                        }
                    }
                    Ok(Value {
                        kind: ValueKind::Vector(elems.into_iter().map(|(_, v)| v.kind).collect()),
                        unit,
                    })
                }
            }
            Expression::Indexed { fc, expr, index } => {
                let expr = self.eval_expr(expr, call_stack)?;
                let index = self.eval_expr(index, call_stack)?;

                let vec = match &expr.kind {
                    ValueKind::Vector(vec) => vec,
                    _ => return Err(EvalError::InvalidIndexedType(*fc, expr)),
                };

                let idx = match &index.kind {
                    ValueKind::Number(idx) if index.unit == Unit::new() => match idx.to_usize() {
                        Some(idx) => idx,
                        // Reject fractions
                        None if idx.fract().abs() != 0.into() => {
                            return Err(EvalError::InvalidVectorIndex(*fc, index))
                        }
                        // Reject values that are too large to fit in a `usize`
                        None => return Err(EvalError::IndexOutOfBounds(*fc, index, expr)),
                    },
                    _ => return Err(EvalError::InvalidVectorIndex(*fc, index)),
                };

                let kind = match vec.get(idx).cloned() {
                    Some(kind) => kind,
                    None => return Err(EvalError::IndexOutOfBounds(*fc, index, expr)),
                };

                Ok(Value {
                    kind,
                    unit: expr.unit,
                })
            }
        }
    }

    // Name might be changed in future
    #[allow(clippy::ptr_arg)]
    pub fn lookup(&self, name: &Name, call_stack: &CallStack) -> Option<Value> {
        if let Some(val) = call_stack.lookup(name) {
            Some(val.clone())
        } else if let Some(val) = self.variables.get(name) {
            Some(val.clone())
        } else if self.functions.contains_key(name)
            || crate::functions::BUILTIN_FUNCTION_NAMES.contains(&&**name)
        {
            Some(Value {
                kind: ValueKind::FunctionRef(name.clone()),
                unit: Unit::new(),
            })
        } else if self.units.contains(name) {
            Some(Value {
                kind: ValueKind::Number(BigDecimal::from(1)),
                unit: Unit::new_named(name.clone()),
            })
        } else {
            self.unit_aliases.get(name).cloned()
        }
    }

    pub fn eval_infix_op(
        &self,
        fc: FC,
        op: InfixOp,
        lhs: &Expression,
        rhs: &Expression,
        call_stack: &mut CallStack,
    ) -> Result<Value, EvalError> {
        let lhs = self.eval_expr(lhs, call_stack)?;
        let rhs = self.eval_expr(rhs, call_stack)?;

        let unit = infix_unit(fc, op, &lhs, &rhs)?;

        macro_rules! zip {
            ($a:expr, $b:expr, $f:expr) => {
                match $a.zip_number($b, &$f) {
                    ValueKindNumberZipResult::Success(val) => val,
                    ValueKindNumberZipResult::ArityMismatch(_, _) => {
                        return Err(EvalError::InfixArityMismatch(fc, op, lhs, rhs))
                    }
                    ValueKindNumberZipResult::KindMismatch(_, _)
                    | ValueKindNumberZipResult::FoundNonNumber(_, _) => {
                        return Err(EvalError::InvalidInfixOperator(fc, op, lhs, rhs))
                    }
                }
            };
        }

        macro_rules! map {
            ($a:expr, $f:expr) => {
                match $a.map_number(&$f) {
                    Some(val) => val,
                    None => return Err(EvalError::InvalidInfixOperator(fc, op, lhs, rhs)),
                }
            };
        }

        match (op, &lhs.kind, &rhs.kind) {
            (InfixOp::Add, a, b) => Ok(Value {
                kind: zip!(a, b, |a, b| a + b),
                unit,
            }),
            (InfixOp::Sub, a, b) => Ok(Value {
                kind: zip!(a, b, |a, b| a - b),
                unit,
            }),
            (InfixOp::Mul, ValueKind::Number(a), b) => Ok(Value {
                kind: map!(b, |x| a * x),
                unit,
            }),
            (InfixOp::Mul, a, ValueKind::Number(b)) => Ok(Value {
                kind: map!(a, |x| b * x),
                unit,
            }),
            (InfixOp::Mul, a, b) => Ok(Value {
                kind: zip!(a, b, |a, b| a * b),
                unit,
            }),
            (InfixOp::Div, ValueKind::Number(a), b) => Ok(Value {
                kind: map!(b, |x| a / x),
                unit,
            }),
            (InfixOp::Div, a, ValueKind::Number(b)) => Ok(Value {
                kind: map!(a, |x| b / x),
                unit,
            }),
            (InfixOp::Div, a, b) => Ok(Value {
                kind: zip!(a, b, |a, b| a / b),
                unit,
            }),
            (InfixOp::Mod, ValueKind::Number(a), b) => Ok(Value {
                kind: map!(b, |x| a % x),
                unit,
            }),
            (InfixOp::Mod, a, ValueKind::Number(b)) => Ok(Value {
                kind: map!(a, |x| b % x),
                unit,
            }),
            (InfixOp::Mod, a, b) => Ok(Value {
                kind: zip!(a, b, |a, b| a % b),
                unit,
            }),
            (InfixOp::Pow, ValueKind::Number(a), ValueKind::Number(b)) => {
                if b.abs().fract() == 0.into() {
                    // Integer power
                    let pow = b.trunc().to_isize().unwrap();

                    let mut res = BigDecimal::from(1);

                    for _ in 0..pow.abs() {
                        res *= a;
                    }

                    if pow.is_negative() {
                        res = res.recip();
                    }

                    Ok(Value {
                        kind: ValueKind::Number(res),
                        unit,
                    })
                } else if lhs.unit == rhs.unit && lhs.unit == Unit::new() {
                    // Float power, only works on unitless values
                    #[cfg(feature = "multi-precision-float")]
                    use rug::ops::Pow;

                    let a = crate::num::float_from_decimal(a);
                    let b = crate::num::float_from_decimal(b);

                    #[cfg(feature = "multi-precision-float")]
                    let res = a.pow(b);
                    #[cfg(not(feature = "multi-precision-float"))]
                    let res = a.powf(b);

                    let res = crate::num::decimal_from_float(&res);
                    Ok(Value {
                        kind: ValueKind::Number(res),
                        unit: Unit::new(),
                    })
                } else {
                    Err(EvalError::InvalidInfixOperator(
                        fc,
                        op,
                        lhs.clone(),
                        rhs.clone(),
                    ))
                }
            }
            (InfixOp::To, _, _) => {
                let lunit = lhs.unit.clone();
                let runit = rhs.unit.clone();

                if lunit == runit {
                    Ok(lhs)
                } else if let Some((name, body)) = self.conversions.get(&(lunit, runit)) {
                    call_stack.push(Some((name.clone(), lhs.clone())).into_iter().collect());

                    let res = self.eval_expr(body, call_stack);

                    call_stack.pop();

                    res
                } else {
                    todo!()
                }
            }
            (InfixOp::Eq, a, b) => {
                if a == b {
                    Ok(lhs.clone())
                } else {
                    Err(EvalError::EqualtyError(fc, op, lhs.clone(), rhs.clone()))
                }
            }
            (InfixOp::Neq, a, b) => {
                if a != b {
                    Ok(Value {
                        kind: ValueKind::Number(1.into()),
                        unit,
                    })
                } else {
                    Err(EvalError::EqualtyError(fc, op, lhs.clone(), rhs.clone()))
                }
            }
            (InfixOp::Gt, ValueKind::Number(a), ValueKind::Number(b)) => {
                if a > b {
                    Ok(Value {
                        kind: ValueKind::Number(1.into()),
                        unit,
                    })
                } else {
                    Err(EvalError::EqualtyError(fc, op, lhs.clone(), rhs.clone()))
                }
            }
            (op, _, _) => Err(EvalError::InvalidInfixOperator(fc, op, lhs, rhs)),
        }
    }
}

fn apply_prefix(fc: FC, prefix: SiPrefix, val: Value) -> Result<Value, EvalError> {
    fn apply_to_value_kind(
        fc: FC,
        prefix: SiPrefix,
        val: &Value,
        kind: &ValueKind,
    ) -> Result<ValueKind, EvalError> {
        match kind {
            ValueKind::FunctionRef(_) => Err(EvalError::InvalidSiPrefix(fc, prefix, val.clone())),
            ValueKind::Number(n) => Ok(ValueKind::Number(&prefix.value() * n)),
            ValueKind::Vector(v) => {
                let vals = v
                    .iter()
                    .map(|vk| apply_to_value_kind(fc, prefix, val, vk))
                    .collect::<Result<_, _>>()?;
                Ok(ValueKind::Vector(vals))
            }
        }
    }
    Ok(Value {
        kind: apply_to_value_kind(fc, prefix, &val, &val.kind)?,
        unit: val.unit,
    })
}

fn infix_unit(fc: FC, op: InfixOp, lhs: &Value, rhs: &Value) -> Result<Unit, UnitError> {
    match op {
        InfixOp::Add | InfixOp::Sub | InfixOp::Mod => {
            if lhs.unit == rhs.unit {
                Ok(lhs.unit.clone())
            } else {
                Err(UnitError::IncompatibleUnitsInfix(
                    fc,
                    op,
                    lhs.unit.clone(),
                    rhs.unit.clone(),
                ))
            }
        }

        InfixOp::Mul => Ok(lhs.unit.multiply(&rhs.unit)),
        InfixOp::Div => Ok(lhs.unit.divide(&rhs.unit)),
        InfixOp::Pow => {
            if rhs.unit != Unit::new() {
                return Err(UnitError::IncompatibleUnitsInfix(
                    fc,
                    op,
                    lhs.unit.clone(),
                    rhs.unit.clone(),
                ));
            }
            match &rhs.kind {
                ValueKind::Number(n) => Ok(lhs.unit.pow(n)),
                _ => Err(UnitError::InvalidPowerValue(
                    fc,
                    lhs.unit.clone(),
                    rhs.kind.clone(),
                )),
            }
        }
        InfixOp::To => Ok(rhs.unit.clone()),
        InfixOp::Eq => {
            if lhs.unit == rhs.unit {
                Ok(lhs.unit.clone())
            } else {
                Err(UnitError::IncompatibleUnitsInfix(
                    fc,
                    op,
                    lhs.unit.clone(),
                    rhs.unit.clone(),
                ))
            }
        }
        InfixOp::Neq => {
            if lhs.unit == rhs.unit {
                Ok(Unit::new())
            } else {
                Err(UnitError::IncompatibleUnitsInfix(
                    fc,
                    op,
                    lhs.unit.clone(),
                    rhs.unit.clone(),
                ))
            }
        }
        InfixOp::Gt => {
            if lhs.unit == rhs.unit {
                Ok(Unit::new())
            } else {
                Err(UnitError::IncompatibleUnitsInfix(
                    fc,
                    op,
                    lhs.unit.clone(),
                    rhs.unit.clone(),
                ))
            }
        }
    }
}

pub enum EvalResult {
    Empty,
    Value(Value),
    PrintValue(Expression, Value),
    VariableSearchResult {
        unit_aliases: BTreeMap<Name, Value>,
        variables: BTreeMap<Name, Value>,
        functions: BTreeMap<Name, Vec<Name>>,
    },
    UnitSearchResult {
        unit: Unit,
        unit_aliases: BTreeMap<Name, ValueKind>,
        variables: BTreeMap<Name, ValueKind>,
    },
}

#[derive(Debug, Error)]
pub enum ItemError {
    #[error("Unit redeclared: {}", .0)]
    UnitRedeclared(Name),
    #[error("Conversion redeclared: from [{}] to [{}]", .from, .to)]
    ConversionRedeclared { from: Unit, to: Unit },
    #[error("Function redefined: {}", .0)]
    FunctionRedefined(Name),

    #[error("Eval error: {}", .0)]
    EvalError(#[from] EvalError),
}

#[derive(Debug, Error)]
pub enum EvalError {
    #[error("Undefined name: {}", .1)]
    UndefinedName(FC, Name),

    #[error("Value type mismatch, found {} [{}]", .1.kind, .1.unit)]
    ValueKindMismatch(FC, Value),

    #[error("Invalid prefix operator {:?} on value {} [{}]", .1, .2.kind, .2.unit)]
    InvalidPrefixOperator(FC, PrefixOp, Value),

    #[error("Invalid infix operator {:?} on {} [{}] and {} [{}]", .1, .2.kind, .2.unit, .3.kind, .3.unit)]
    InvalidInfixOperator(FC, InfixOp, Value, Value),

    #[error("Invalid SI-prefix {:?} on value {} [{}]", .1, .2.kind, .2.unit)]
    InvalidSiPrefix(FC, SiPrefix, Value),

    #[error("Equality assertion error {:?} on values {} [{}] and {} [{}]", .1, .2.kind, .2.unit, .3.kind, .3.unit)]
    EqualtyError(FC, InfixOp, Value, Value),

    #[error("Calling a value as a function that's not a function type: {}", .1.kind)]
    CallOnNonFunction(FC, Value),

    #[error("Incorrect amount of function arguments: {} called with {} argument(s), but {} were expected", .base.kind, .num_args_applied, .num_args_expected)]
    CallArgumentMismatch {
        fc: FC,
        base: Value,
        num_args_expected: usize,
        num_args_applied: usize,
    },

    #[error("Arity mismatch on infix operator {:?} on {} [{}] and {} [{}]", .1, .2.kind, .2.unit, .3.kind, .3.unit)]
    InfixArityMismatch(FC, InfixOp, Value, Value),

    #[error("Unit error: {}", .0)]
    UnitError(#[from] UnitError),

    #[error("Attempted to index a non-vector value: {} [{}]", .1.kind, .1.unit)]
    InvalidIndexedType(FC, Value),

    #[error("Index {} is out of bounds of vector value: {} [{}]", .1.kind, .2.kind, .2.unit)]
    IndexOutOfBounds(FC, Value, Value),

    #[error("Vector indices must be unitless natural numbers but got {} [{}]", .1.kind, .1.unit)]
    InvalidVectorIndex(FC, Value),
}

#[derive(Debug, Error)]
pub enum UnitError {
    #[error("Unit mismatch, found ({}) but expected ({})", .found, .expected)]
    UnitMismatch { fc: FC, expected: Unit, found: Unit },

    #[error("Incompatible units ({}) and ({}) for operation {:?}", .2, .3, .1)]
    IncompatibleUnitsInfix(FC, InfixOp, Unit, Unit),

    #[error("Invalid power on unit ({}): {}", .1, .2)]
    InvalidPowerValue(FC, Unit, ValueKind),
}
