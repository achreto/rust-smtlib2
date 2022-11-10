// Smt2 Code Generation - Function Declaration
//
//
// MIT License
//
// Copyright (c) 2022 Reto Achermann, University of British Columbia.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! Function Declaration

use std::fmt::{self, Write};
use std::hash::Hash;

use super::Formatter;

// a numeric literal <numeral>
// a decimal literal <decimal>
// a string literal <string>
// a binary literal <binary>
// a hex literal <hex>
// an <identifier>, which is one of:
// a symbol: <symbol>
// an indexed identifier: ( _ <symbol> <numeral>+ )
// a qualified-identifier: <identifier>
// or ( as <identifier> <sort>)
// a function application: ( <qualified-identifier> <expr>+)
// a forall-expression: ( forall ( (<symbol> <sort>)+ ) <expr>)
// an exists-expression: ( exists ( (<symbol> <sort>)+ ) <expr>)
// a let-expression: ( let ( (<symbol> <expr>)+ ) <expr>)
// an attributed expression: ( ! <expr> <attribute>+)

/// Binds the expression to a variable
#[derive(Clone, Hash)]
pub struct VarBinding {
    symbol: String,
    term: Term,
}

impl VarBinding {
    pub fn new(symbol: String, term: Term) -> Self {
        Self { symbol, term }
    }

    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "({} ", self.symbol)?;
        self.term.fmt(fmt)?;
        write!(fmt, ")")
    }
}

impl fmt::Display for VarBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}

/// Defines a variable with a type
#[derive(Clone, Hash)]
pub struct SortedVar {
    pub ident: String,
    pub sort: String,
}

impl SortedVar {
    pub fn new(ident: String, sort: String) -> Self {
        Self { ident, sort }
    }

    pub fn fmt(&self, fmt: &mut Formatter<'_>, with_names: bool) -> fmt::Result {
        if with_names {
            write!(fmt, "({} {})", self.ident, self.sort)
        } else {
            write!(fmt, "{}", self.sort)
        }
    }
}

impl fmt::Display for SortedVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret), true).unwrap();
        write!(f, "{}", ret)
    }
}

#[derive(Clone, Hash)]
pub struct Pattern {
    pub symbols: Vec<String>,
}

impl Pattern {
    pub fn new(symbols: Vec<String>) -> Self {
        Self { symbols }
    }

    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        if self.symbols.len() == 1 {
            write!(fmt, "{}", self.symbols[0])
        } else {
            for (i, sym) in self.symbols.iter().enumerate() {
                if i == 0 {
                    write!(fmt, "({}", sym)?;
                } else {
                    write!(fmt, " {}", sym)?;
                }
            }
            write!(fmt, ")")
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}

#[derive(Clone, Hash)]
pub struct MatchCase {
    pattern: Pattern,
    term: Term,
}

impl MatchCase {
    pub fn new(pattern: Pattern, term: Term) -> Self {
        Self { pattern, term }
    }

    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "(")?;
        self.pattern.fmt(fmt)?;
        write!(fmt, " ")?;
        self.term.fmt(fmt)?;
        write!(fmt, ")")
    }
}

impl fmt::Display for MatchCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}

#[derive(Clone, Hash)]
pub struct Attribute {
    keyword: String,
    value: Option<String>,
}

impl Attribute {
    pub fn new(keyword: String) -> Self {
        Self {
            keyword,
            value: None,
        }
    }

    pub fn with_value(keyword: String, value: String) -> Self {
        Self {
            keyword,
            value: Some(value),
        }
    }

    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, ":{} ", self.keyword)?;
        if let Some(value) = &self.value {
            write!(fmt, "{}", value)?;
        }
        Ok(())
    }
}

impl fmt::Display for Attribute {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}

/// Represents an expression in SMT2
///
/// # Example
///
/// ; expression
/// (+ a b)
///
#[derive(Clone, Hash)]
pub enum Term {
    Numeral(u64),
    // Decimal(f64),
    String(String),
    Binary(bool),
    // Hex(String),
    Identifier(String),
    QualifiedIdentifier(SortedVar),
    FunctionApplication(String, Vec<Term>),
    Forall(Vec<SortedVar>, Box<Term>),
    Exists(Vec<SortedVar>, Box<Term>),
    Let(Vec<VarBinding>, Box<Term>),
    Match(Box<Term>, Vec<MatchCase>),
    AttributedTerm(Box<Term>, Vec<Attribute>),
}

impl Term {
    pub fn num(num: u64) -> Self {
        Term::Numeral(num)
    }

    pub fn string(s: String) -> Self {
        Term::String(s)
    }

    pub fn binary(b: bool) -> Self {
        Term::Binary(b)
    }

    pub fn bv_zero_extend(term: Term, num: u64) -> Self {
        let ident = format!("(_ zero_extend {})", num);
        Term::FunctionApplication(ident, vec![term])
    }

    pub fn bv_extract(term: Term, s: u64, e: u64) -> Self {
        let ident = format!("(_ extract {} {})", e, s);
        Term::FunctionApplication(ident, vec![term])
    }

    pub fn bv_concat(bv: Vec<Term>) -> Self {
        Term::FunctionApplication("concat".to_string(), bv)
    }

    pub fn ident(s: String) -> Self {
        Term::Identifier(s)
    }

    pub fn ifelse(cond: Term, then: Term, other: Term) -> Self {
        Term::FunctionApplication("ite".to_string(), vec![cond, then, other])
    }

    pub fn attributed(term: Term, attrs: Vec<Attribute>) -> Self {
        Term::AttributedTerm(Box::new(term), attrs)
    }

    pub fn named(term: Term, name: String) -> Self {
        Term::AttributedTerm(
            Box::new(term),
            vec![Attribute::with_value(String::from("named"), name)],
        )
    }

    pub fn letexpr(vars: Vec<VarBinding>, expr: Term) -> Self {
        Term::Let(vars, Box::new(expr))
    }

    pub fn fn_apply(name: String, args: Vec<Term>) -> Self {
        Term::FunctionApplication(name, args)
    }

    pub fn bvand(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvand".to_string(), vec![lhs, rhs])
    }

    pub fn bvor(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvor".to_string(), vec![lhs, rhs])
    }

    pub fn bvxor(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvxor".to_string(), vec![lhs, rhs])
    }

    pub fn bvshl(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvshl".to_string(), vec![lhs, rhs])
    }

    pub fn bvshr(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvlshr".to_string(), vec![lhs, rhs])
    }

    pub fn bveq(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("=".to_string(), vec![lhs, rhs])
    }

    pub fn bvne(lhs: Term, rhs: Term) -> Self {
        Term::lnot(Term::bveq(lhs, rhs))
    }

    pub fn bvadd(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvadd".to_string(), vec![lhs, rhs])
    }

    pub fn bvsub(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvsub".to_string(), vec![lhs, rhs])
    }

    pub fn bvdiv(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvudiv".to_string(), vec![lhs, rhs])
    }

    pub fn bvmul(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvmul".to_string(), vec![lhs, rhs])
    }

    pub fn bvlt(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvult".to_string(), vec![lhs, rhs])
    }

    pub fn bvle(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvule".to_string(), vec![lhs, rhs])
    }

    pub fn bvge(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvuge".to_string(), vec![lhs, rhs])
    }

    pub fn bvgt(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("bvugt".to_string(), vec![lhs, rhs])
    }

    pub fn land(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("and".to_string(), vec![lhs, rhs])
    }

    pub fn lor(lhs: Term, rhs: Term) -> Self {
        Term::FunctionApplication("or".to_string(), vec![lhs, rhs])
    }

    pub fn lnot(expr: Term) -> Self {
        Term::FunctionApplication("not".to_string(), vec![expr])
    }

    pub fn bvnot(expr: Term) -> Self {
        Term::FunctionApplication("bvnot".to_string(), vec![expr])
    }

    pub fn eq(self, other: Term) -> Term {
        Term::FunctionApplication("=".to_string(), vec![self, other])
    }

    pub fn implies(self, other: Term) -> Term {
        Term::FunctionApplication("=>".to_string(), vec![self, other])
    }

    pub fn forall(vars: Vec<SortedVar>, expr: Term) -> Self {
        Term::Forall(vars, Box::new(expr))
    }

    pub fn exists(vars: Vec<SortedVar>, expr: Term) -> Self {
        Term::Exists(vars, Box::new(expr))
    }

    pub fn is_literal(&self) -> bool {
        match self {
            Term::Numeral(_)
            // | Term::Decimal(_)
            | Term::String(_)
            | Term::Binary(_)
            | Term::Identifier(_) => true,
            _ => false,
        }
    }

    /// Formats the variant using the given formatter.
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Term::Numeral(n) => write!(fmt, "#x{:016x}", n),
            // Term::Decimal(n) => write!(fmt, "{}", n),
            Term::String(s) => write!(fmt, "\"{}\"", s),
            Term::Binary(b) => {
                if *b {
                    write!(fmt, "true")
                } else {
                    write!(fmt, "false")
                }
            }
            // Term::Hex(s) => write!(fmt, "{}", s),
            Term::Identifier(s) => write!(fmt, "{}", s),
            Term::QualifiedIdentifier(s) => {
                write!(fmt, "(as {} {})", s.ident, s.sort)
            }
            Term::FunctionApplication(s, args) => {
                // let oneline = args.len() < 4 && args.iter().all(|a| a.is_literal());
                // if oneline {
                //     write!(fmt, "({} ", s)?;
                // } else {
                //     writeln!(fmt, "({} ", s)?;
                // }
                writeln!(fmt, "({} ", s)?;
                fmt.indent(|fmt| {
                    for (_i, arg) in args.iter().enumerate() {
                        // if oneline && i > 0 {
                        //     write!(fmt, " ")?;
                        // }
                        arg.fmt(fmt)?;
                        // if !oneline {
                        writeln!(fmt)?;
                        // }
                    }
                    Ok(())
                })?;
                write!(fmt, ")")
            }
            Term::Forall(vars, term) => {
                writeln!(fmt, "(forall (")?;
                fmt.indent(|fmt| {
                    for (i, var) in vars.iter().enumerate() {
                        if i > 0 {
                            write!(fmt, " ")?;
                        }
                        var.fmt(fmt, true)?;
                    }
                    Ok(())
                })?;
                writeln!(fmt, ") ")?;
                fmt.indent(|fmt| term.fmt(fmt))?;
                write!(fmt, "\n)")
            }
            Term::Exists(vars, term) => {
                writeln!(fmt, "(exists (")?;
                fmt.indent(|fmt| {
                    for (i, var) in vars.iter().enumerate() {
                        if i > 0 {
                            write!(fmt, " ")?;
                        }
                        var.fmt(fmt, true)?;
                    }
                    Ok(())
                })?;
                write!(fmt, ") ")?;
                fmt.indent(|fmt| term.fmt(fmt))?;
                write!(fmt, "\n)")
            }
            Term::Let(vars, expr) => {
                writeln!(fmt, "(let (")?;
                fmt.indent(|fmt| {
                    for var in vars.iter() {
                        var.fmt(fmt)?;
                        writeln!(fmt)?;
                    }
                    Ok(())
                })?;
                write!(fmt, ") ")?;
                expr.fmt(fmt)?;
                write!(fmt, ")")
            }
            Term::Match(term, cases) => {
                writeln!(fmt, "(match ")?;
                term.fmt(fmt)?;
                writeln!(fmt, " (")?;
                fmt.indent(|f| {
                    for case in cases.iter() {
                        case.fmt(f)?;
                        writeln!(f)?;
                    }
                    Ok(())
                })?;
                writeln!(fmt, " )")?;
                write!(fmt, ")")
            }
            Term::AttributedTerm(term, attrs) => {
                writeln!(fmt, "(! ")?;
                fmt.indent(|f| term.fmt(f))?;
                for (i, a) in attrs.iter().enumerate() {
                    if i != 0 {
                        write!(fmt, " ")?;
                    }
                    a.fmt(fmt)?;
                }
                writeln!(fmt, ")")
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}

use std::ops::Add;
use std::ops::BitAnd;
use std::ops::BitOr;
use std::ops::BitXor;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Not;
use std::ops::Shl;
use std::ops::Shr;
use std::ops::Sub;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Arithmetic Operations: + - * /
////////////////////////////////////////////////////////////////////////////////////////////////////

impl Add for Term {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Term::bvadd(self, other)
    }
}

impl Sub for Term {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Term::bvsub(self, other)
    }
}

impl Div for Term {
    // The division of rational numbers is a closed operation.
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Term::bvdiv(self, rhs)
    }
}

impl Mul for Term {
    // The multiplication of rational numbers is a closed operation.
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Term::bvmul(self, rhs)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Bitwise Operations: & | ^ -
////////////////////////////////////////////////////////////////////////////////////////////////////

impl BitAnd for Term {
    type Output = Self;

    // rhs is the "right-hand side" of the expression `a & b`
    fn bitand(self, rhs: Self) -> Self::Output {
        Term::bvand(self, rhs)
    }
}

impl BitOr for Term {
    type Output = Self;

    // rhs is the "right-hand side" of the expression `a | b`
    fn bitor(self, rhs: Self) -> Self::Output {
        Term::bvor(self, rhs)
    }
}

impl BitXor for Term {
    type Output = Self;

    // rhs is the "right-hand side" of the expression `a ^ b`
    fn bitxor(self, rhs: Self) -> Self::Output {
        Term::bvxor(self, rhs)
    }
}

impl Neg for Term {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Term::bvnot(self)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Shifts
////////////////////////////////////////////////////////////////////////////////////////////////////

impl Shl<Term> for Term {
    type Output = Self;

    fn shl(self, rhs: Self) -> Self::Output {
        Term::bvshl(self, rhs)
    }
}

impl Shr<Term> for Term {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Term::bvshr(self, rhs)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Logic Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

impl Not for Term {
    type Output = Self;

    fn not(self) -> Self::Output {
        Term::lnot(self)
    }
}

// Want: operator overloading for comparisons
