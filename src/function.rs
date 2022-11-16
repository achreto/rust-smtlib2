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

use std::fmt::{self, Display, Write};
use std::hash::Hash;

use super::Formatter;
use super::{SortedVar, Term};

/// Represents a function declaration in SMT2
///
/// # Example
///
/// ; data type
/// (declare-fun x () Bool)
///
#[derive(Hash, PartialEq, Eq)]
pub struct Function {
    /// the name of the datatype
    name: String,
    /// the number of type parameters
    args: Vec<SortedVar>,
    /// the fields of the datatype
    rettype: String,
    /// the body of the expression
    body: Option<Term>,
    /// a comment string for the requires clause
    comment: Option<String>,
}

impl Function {
    /// creates a new requires expression
    pub fn new(name: String, rettype: String) -> Self {
        Function {
            name,
            args: Vec::new(),
            rettype,
            body: None,
            comment: None,
        }
    }

    /// adds a comment to the requires expression
    pub fn add_comment(&mut self, comment: String) -> &mut Self {
        self.comment = Some(comment.replace('\n', ";\n"));
        self
    }

    /// adds a field to the datatype
    pub fn add_arg(&mut self, name: String, ty: String) -> &mut Self {
        self.args.push(SortedVar::new(name, ty));
        self
    }

    /// adds a body to the function
    pub fn add_body(&mut self, body: Term) -> &mut Self {
        self.body = Some(body);
        self
    }

    /// Formats the variant using the given formatter.
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        if let Some(c) = &self.comment {
            writeln!(fmt, ";; {}", c)?;
        }

        if self.body.is_some() {
            write!(fmt, "(define-fun {} (", self.name)?;
        } else {
            write!(fmt, "(declare-fun {} (", self.name)?;
        }

        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(fmt, " ")?;
            }
            if self.body.is_some() {
                arg.fmt(fmt, true)?;
            } else {
                arg.fmt(fmt, false)?;
            }
        }

        write!(fmt, ") {}", self.rettype)?;
        if let Some(body) = &self.body {
            writeln!(fmt)?;
            fmt.indent(|fmt| body.fmt(fmt))?;
            writeln!(fmt, "\n)\n")
        } else {
            writeln!(fmt, ")\n")
        }
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}
