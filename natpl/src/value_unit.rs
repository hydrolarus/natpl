use fraction::*;
use std::{collections::BTreeMap, fmt::Display};

use crate::{num::dec_in_scientific_notation, num::max_precision, syntax::Name};

#[derive(Debug, Clone)]
pub struct Value {
    pub kind: ValueKind,
    pub unit: Unit,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ValueKind {
    FunctionRef(Name),
    Number(BigDecimal),
    String(String),
    Vector(Vec<ValueKind>),
}

pub enum ValueKindNumberZipResult {
    Success(ValueKind),
    ArityMismatch(ValueKind, ValueKind),
    KindMismatch(ValueKind, ValueKind),
    FoundNonNumber(ValueKind, ValueKind),
}

impl ValueKind {
    pub fn map_number(&self, f: &impl Fn(&BigDecimal) -> BigDecimal) -> Option<ValueKind> {
        match self {
            ValueKind::FunctionRef(_) | ValueKind::String(_) => None,
            ValueKind::Number(n) => Some(ValueKind::Number(f(n))),
            ValueKind::Vector(elems) => {
                let elems = elems
                    .iter()
                    .map(|e| e.map_number(f))
                    .collect::<Option<_>>()?;
                Some(ValueKind::Vector(elems))
            }
        }
    }

    pub fn zip_number(
        &self,
        other: &Self,
        f: &impl Fn(&BigDecimal, &BigDecimal) -> BigDecimal,
    ) -> ValueKindNumberZipResult {
        match (self, other) {
            (ValueKind::Number(a), ValueKind::Number(b)) => {
                ValueKindNumberZipResult::Success(ValueKind::Number(f(a, b)))
            }
            (ValueKind::Vector(a), ValueKind::Vector(b)) => {
                if a.len() != b.len() {
                    return ValueKindNumberZipResult::ArityMismatch(self.clone(), other.clone());
                }

                let mut elems = Vec::with_capacity(a.len());

                for (a, b) in a.iter().zip(b) {
                    match a.zip_number(b, f) {
                        ValueKindNumberZipResult::Success(v) => elems.push(v),
                        err => return err,
                    }
                }

                ValueKindNumberZipResult::Success(ValueKind::Vector(elems))
            }
            (ValueKind::FunctionRef(_), _) | (_, ValueKind::FunctionRef(_)) => {
                ValueKindNumberZipResult::FoundNonNumber(self.clone(), other.clone())
            }
            (a, b) => ValueKindNumberZipResult::KindMismatch(a.clone(), b.clone()),
        }
    }
}

fn display_bigdec(num: &BigDecimal) -> String {
    let (int, dec, exp, sign) = dec_in_scientific_notation(num);

    if exp < -50 {
        return "≈0".to_string();
    }

    let exp_str = if exp == 0 {
        "".to_string()
    } else {
        format!("x10^{}", exp)
    };

    if (0..4).contains(&exp) {
        if dec.len() < exp as usize {
            format!("{:.prec$}", num, prec = num.get_precision().min(4))
        } else {
            format!("{:.prec$}", num, prec = dec.len().min(4) - exp as usize)
        }
    } else if (-3..0).contains(&exp) {
        format!(
            "{:.prec$}",
            num,
            prec = (dec.len() + (-exp) as usize).min(4)
        )
    } else if dec.is_empty() {
        format!("{}{}{}", sign, int, exp_str)
    } else {
        let dec = max_precision(&dec, 3);
        format!("{}{}.{}{}", sign, int, dec, exp_str)
    }
}

impl Display for ValueKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueKind::FunctionRef(name) => f.write_fmt(format_args!("<function {}>", name)),
            ValueKind::String(val) => f.write_fmt(format_args!("{:?}", val)),
            ValueKind::Number(num) => f.write_str(&display_bigdec(num)),
            ValueKind::Vector(nums) => {
                f.write_str("(")?;
                for (i, e) in nums.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    f.write_fmt(format_args!("{}", e))?;
                }
                // trailing comma for 1-vectors
                if nums.len() == 1 {
                    f.write_str(",")?;
                }
                f.write_str(")")
            }
        }
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq, Hash)]
pub struct Unit {
    parts: BTreeMap<Name, BigDecimal>,
}

impl Unit {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn new_named(name: Name) -> Self {
        let mut this = Self::new();
        this.parts.insert(name, 1.into());
        this
    }

    pub fn singleton(&self) -> Option<&Name> {
        if self.parts.len() != 1 {
            None
        } else {
            let (name, p) = self.parts.iter().next()?;
            if *p != 1.into() {
                None
            } else {
                Some(name)
            }
        }
    }

    pub fn multiply(&self, other: &Unit) -> Unit {
        let mut parts = self.parts.clone();

        for (name, val) in &other.parts {
            let total = parts
                .entry(name.clone())
                .and_modify(|e| *e += val)
                .or_insert_with(|| val.clone())
                .clone();

            if total.abs() == 0.into() {
                parts.remove(name);
            }
        }

        Unit { parts }
    }

    pub fn divide(&self, other: &Unit) -> Unit {
        let mut parts = self.parts.clone();

        for (name, val) in &other.parts {
            let total = parts
                .entry(name.clone())
                .and_modify(|e| *e -= val)
                .or_insert_with(|| -val.clone())
                .clone();

            if total.abs() == 0.into() {
                parts.remove(name);
            }
        }

        Unit { parts }
    }

    pub fn pow(&self, n: &BigDecimal) -> Unit {
        let sign = n.sign();
        let n_add = n.abs();

        let parts = self
            .parts
            .iter()
            .filter_map(|(k, v)| {
                let v = v * &n_add;
                if v.abs() == 0.into() {
                    None
                } else if sign == Some(Sign::Minus) {
                    Some((k.clone(), -v))
                } else {
                    Some((k.clone(), v))
                }
            })
            .collect();

        Unit { parts }
    }
}

impl Display for Unit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, (name, pow)) in self.parts.iter().enumerate() {
            if i > 0 {
                f.write_str(" ")?;
            }

            f.write_str(name)?;

            if *pow != 1.into() {
                f.write_fmt(format_args!("^{}", display_bigdec(pow)))?;
            }
        }

        Ok(())
    }
}
