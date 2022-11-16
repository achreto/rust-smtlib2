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

use super::Formatter;

#[derive(Hash, PartialEq, Eq)]
pub enum InfoFlag {
    AllStatistics,
    AssertionStackLevels,
    Authors,
    ErrorBehaviour,
    Name,
    ReasonUnknown,
    Version,
    Keyword(String),
}

impl InfoFlag {
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        use InfoFlag::*;
        match self {
            AllStatistics => write!(fmt, ":all-statistics"),
            AssertionStackLevels => write!(fmt, ":assertion-stack-levels"),
            Authors => write!(fmt, ":authors"),
            ErrorBehaviour => write!(fmt, ":error-behaviour"),
            Name => write!(fmt, ":name"),
            ReasonUnknown => write!(fmt, ":reason-unknown"),
            Version => write!(fmt, ":version"),
            Keyword(s) => write!(fmt, ":{}", s),
        }
    }
}

impl fmt::Display for InfoFlag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret))?;
        write!(f, "{}", ret)
    }
}
