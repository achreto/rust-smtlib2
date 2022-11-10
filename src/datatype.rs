// Smt2 Code Generation - Datatype Declaration
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

//! Datatype Declaration

use std::fmt::{self, Display, Write};
use std::hash::Hash;

use crate::{Function, Smt2Context, Term};

use super::Formatter;

#[derive(Hash)]
struct DatatTypeField {
    name: String,
    ty: String,
}

impl DatatTypeField {
    fn new(name: String, ty: String) -> Self {
        DatatTypeField { name, ty }
    }

    /// Formats the variant using the given formatter.
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "({} {})", self.name, self.ty)
    }
}

impl Display for DatatTypeField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}

/// Represents a datatype declaration in SMT2
///
/// # Example
///
/// ; data type
/// (declare-datatypes ((State 0))) ((State/State (State/State/Field Int)))
///
#[derive(Hash)]
pub struct DataType {
    /// the name of the datatype
    name: String,
    /// the number of type parameters
    arty: u8,
    /// the fields of the datatype
    fields: Vec<DatatTypeField>,
    /// a comment string for the requires clause
    comment: Option<String>,
}

impl DataType {
    /// creates a new requires expression
    pub fn new(name: String, arty: u8) -> Self {
        DataType {
            name,
            arty,
            fields: Vec::new(),
            comment: None,
        }
    }

    /// adds a comment to the requires expression
    pub fn add_comment(&mut self, comment: String) -> &mut Self {
        self.comment = Some(comment.replace('\n', ";\n"));
        self
    }

    /// adds a field to the datatype
    pub fn add_field(&mut self, name: String, ty: String) -> &mut Self {
        self.fields.push(DatatTypeField::new(name, ty));
        self
    }

    pub fn to_field_accessor(&self) -> Smt2Context {
        let mut smt = Smt2Context::new();
        for (_i, field) in self.fields.iter().enumerate() {
            let name = format!("{}.get!", field.name);
            let mut f = Function::new(name, field.ty.clone());
            f.add_arg("s@".to_string(), format!("{}_t", self.name));

            f.add_body(Term::fn_apply(
                format!("{}", field.name),
                vec![Term::ident("s@".to_string())],
            ));

            smt.function(f);
        }

        for (i, field) in self.fields.iter().enumerate() {
            let name = format!("{}.set!", field.name);
            let mut f = Function::new(name, format!("{}_t", self.name));
            f.add_arg("s@".to_string(), format!("{}_t", self.name));

            f.add_arg("v@".to_string(), field.ty.clone());

            let mut args = Vec::new();
            for (j, f2) in self.fields.iter().enumerate() {
                if i == j {
                    args.push(Term::ident("v@".to_string()));
                } else {
                    args.push(Term::fn_apply(
                        format!("{}.get!", f2.name),
                        vec![Term::ident("s@".to_string())],
                    ));
                }
            }

            f.add_body(Term::fn_apply(format!("{}", self.name), args));

            smt.function(f);
        }
        smt
    }

    /// Formats the variant using the given formatter.
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        if let Some(c) = &self.comment {
            writeln!(fmt, ";; {}", c)?;
        }

        writeln!(
            fmt,
            "(declare-datatypes (({}_t {})) (",
            self.name, self.arty
        )?;

        fmt.indent(|fmt| {
            write!(fmt, "(({} ", self.name)?;
            for (i, f) in self.fields.iter().enumerate() {
                if i > 0 {
                    write!(fmt, " ")?;
                }
                f.fmt(fmt)?;
            }
            write!(fmt, "))")
        })?;
        writeln!(fmt, "))")?;

        Ok(())
    }
}

impl Display for DataType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret)).unwrap();
        write!(f, "{}", ret)
    }
}
