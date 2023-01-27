// Rosette Code Generation Library
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

//! Smt2 Code Generation Library

use std::fmt;
use std::fmt::Write as _;
use std::fs::File;
use std::io::Write as _;
use std::path::PathBuf;

// modules
mod context;
mod datatype;
mod formatter;
mod function;
mod infoflag;
mod options;
mod propliteral;
mod sort;
mod term;
mod variable;

pub use context::{Smt2Command, Smt2Context};
pub use datatype::DataType;
use formatter::Formatter;
pub use function::Function;
pub use infoflag::InfoFlag;
pub use options::Smt2Option;
pub use propliteral::PropLiteral;
pub use sort::{Sort, SortDecl, SortDef};
pub use term::{Attribute, MatchCase, Pattern, SortedVar, Term, VarBinding};
pub use variable::VarDecl;

/// defines a smtlib2 expression

/// defines a rosette file
pub struct Smt2File {
    /// the pathname of the file
    path: PathBuf,
    /// the document string
    doc: String,
    // the statemetns
    context: Smt2Context,
}

/// implementation of the Smt2File
impl Smt2File {
    /// creates a new rosette file
    pub fn new(path: PathBuf, doc: String) -> Self {
        Smt2File {
            path,
            doc,
            context: Smt2Context::new(),
        }
    }

    pub fn with_context(path: PathBuf, doc: String, context: Smt2Context) -> Self {
        Smt2File { path, doc, context }
    }

    pub fn with_default_opts(path: PathBuf, doc: String) -> Self {
        let mut context = Smt2Context::new();

        let options = vec![
            "auto_config false",
            "smt.mbqi false",
            "smt.case_split 3",
            "smt.qi.eager_threshold 100.0",
            "smt.delay_units true",
            "smt.arith.solver 2",
            "smt.arith.nl false",
        ];

        for o in options {
            context.set_option(Smt2Option::Attribute(Attribute::new(String::from(o))));
        }

        Smt2File { path, doc, context }
    }

    pub fn file(&self) -> &PathBuf {
        &self.path
    }

    pub fn as_context(&self) -> &Smt2Context {
        &self.context
    }

    pub fn as_context_mut(&mut self) -> &mut Smt2Context {
        &mut self.context
    }

    pub fn to_context(self) -> Smt2Context {
        self.context
    }

    // formats the current context into smtlib2 syntax
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        if !self.doc.is_empty() && !fmt.compact() {
            write!(fmt, "; {}\n\n\n", self.doc)?;
        }

        self.context.fmt(fmt)
    }

    pub fn extend_and_save(&self, other: &Smt2Context) {
        self.extend_and_save_as(other, &self.path);
    }

    pub fn extend_and_save_as(&self, other: &Smt2Context, path: &PathBuf) {
        let mut file = File::create(path).expect("failed to create the file");

        let mut buf = String::new();
        self.fmt(&mut Formatter::new(&mut buf, false))
            .expect("failed to format smtlib2 file");
        other
            .fmt(&mut Formatter::new(&mut buf, false))
            .expect("failed to format smtlib2 file");

        file.write_all(buf.as_bytes())
            .expect("failed to write to file");
        file.sync_all().expect("failed to sync the file");
    }

    /// saves the rosette file
    pub fn save(&self) {
        // write the file, return IOError otherwise

        // // grab the stdout
        // let s = match String::from_utf8(output.stdout) {
        //     Ok(v) => v,
        //     Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        // };

        // // if it's empty, assume error
        // if s.is_empty() {
        //     let e = match String::from_utf8(output.stderr) {
        //         Ok(v) => v,
        //         Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        //     };
        //     println!("rosette failure!");
        //     println!("{}", e);
        // }
        // // return the output caputured from stdout
        // // TODO: properly handle errors
        // s
    }
}

impl fmt::Display for Smt2File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret, false))?;
        write!(f, "{ret}")
    }
}
