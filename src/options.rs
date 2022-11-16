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

//! Smt2 Code: Options

use std::fmt;
use std::fmt::Write;
use std::hash::Hash;

use super::Attribute;
use super::Formatter;

#[derive(Hash, PartialEq, Eq)]
pub enum Smt2Option {
    DiagnosticOutputChannel(String),
    GlobalDeclarations(bool),
    InteractiveMode(bool),
    ProduceAssertions(bool),
    ProduceAssignments(bool),
    ProduceModels(bool),
    ProduceProofs(bool),
    ProduceUnsatAssumptions(bool),
    ProduceUnsatCores(bool),
    RandomSeed(u64),
    RegularOutputChannel(String),
    ReproducibleResourceLimit(u64),
    Verbosity(u64),
    Attribute(Attribute),
}

impl Smt2Option {
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        use Smt2Option::*;
        match self {
            DiagnosticOutputChannel(s) => write!(fmt, ":diagnostic-output-channel {}", s),
            GlobalDeclarations(b) => write!(fmt, ":global-declarations {}", b),
            InteractiveMode(b) => write!(fmt, ":interactive-mode {}", b),
            ProduceAssertions(b) => write!(fmt, ":produce-assertions {}", b),
            ProduceAssignments(b) => write!(fmt, ":produce-assignments {}", b),
            ProduceModels(b) => write!(fmt, ":produce-models {}", b),
            ProduceProofs(b) => write!(fmt, ":produce-proofs {}", b),
            ProduceUnsatAssumptions(b) => write!(fmt, ":produce-unsat-assumptions {}", b),
            ProduceUnsatCores(b) => write!(fmt, ":produce-unsat-cores {}", b),
            RandomSeed(u) => write!(fmt, ":random-seed {}", u),
            RegularOutputChannel(s) => write!(fmt, ":regular-output-channel {}", s),
            ReproducibleResourceLimit(u) => write!(fmt, ":reproducible-resource-limit {}", u),
            Verbosity(u) => write!(fmt, ":verbosity {}", u),
            Attribute(s) => s.fmt(fmt),
        }
    }
}

impl fmt::Display for Smt2Option {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret))?;
        write!(f, "{}", ret)
    }
}
