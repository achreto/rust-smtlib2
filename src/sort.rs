// SMTLIB2 Code Generation Library
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

//! Smt2 Code: Sorts

use std::fmt;
use std::fmt::Write;
use std::hash::Hash;

use super::Formatter;

#[derive(Hash, PartialEq, Eq)]
pub struct SortDecl {
    pub name: String,
    pub arity: usize,
}

impl SortDecl {
    pub fn new(name: String, arity: usize) -> Self {
        Self { name, arity }
    }

    // formats the current context into smtlib2 syntax
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        writeln!(fmt, "(declare-sort {} {})", self.name, self.arity)
    }
}

impl fmt::Display for SortDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret, false))?;
        writeln!(f, "{}", ret)
    }
}

#[derive(Hash, PartialEq, Eq)]
pub struct SortDef {
    pub name: String,
    pub params: Vec<String>,
    pub def: String,
}

impl SortDef {
    pub fn new(name: String, def: String) -> Self {
        Self {
            name,
            params: Vec::new(),
            def,
        }
    }

    pub fn add_param(&mut self, param: String) -> &mut Self {
        self.params.push(param);
        self
    }

    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "(define-sort {} (", self.name)?;
        for param in &self.params {
            write!(fmt, "({})", param)?;
        }
        writeln!(fmt, ") {})", self.def)
    }
}

impl fmt::Display for SortDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret, false))?;
        write!(f, "{}", ret)
    }
}

/// prop literals
#[derive(Hash, PartialEq, Eq)]
pub enum Sort {
    Declare(SortDecl),
    Define(SortDef),
    // (define-sort R () Real)
}

impl Sort {
    pub fn new_def(name: String, def: String) -> Self {
        Sort::Define(SortDef::new(name, def))
    }

    pub fn new_decl(name: String, arity: usize) -> Self {
        Sort::Declare(SortDecl::new(name, arity))
    }

    // formats the current context into smtlib2 syntax
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Declare(sort) => sort.fmt(fmt),
            Sort::Define(sort) => sort.fmt(fmt),
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Declare(sort) => write!(f, "{}", sort),
            Sort::Define(sort) => write!(f, "{}", sort),
        }
    }
}
