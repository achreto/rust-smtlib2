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

//! Smt2 Code: Prop Literals

use std::fmt;
use std::fmt::Write;
use std::hash::Hash;

use super::{
    Attribute, DataType, Formatter, Function, InfoFlag, PropLiteral, Smt2Option, Sort, Term,
    VarDecl,
};

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Smt2Command {
    Assert(Term),
    CheckSat,
    CheckSatAssuming(Vec<PropLiteral>),
    Const(VarDecl),
    DataType(DataType),
    Function(Function),
    Sort(Sort),
    Echo(String),
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo(InfoFlag),
    GetModel,
    GetOption(Smt2Option),
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue(Vec<Term>),
    Level(Smt2Context),
    Reset,
    ResetAssertions,
    SetInfo(InfoFlag),
    SetLogic(String),
    SetOption(Smt2Option),
    Section(String),
    SubSection(String),
    Comment(String),
    Raw(String),
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Smt2Context {
    commands: Vec<Smt2Command>,
    numcmd: usize,
}

impl Smt2Context {
    pub fn new() -> Self {
        Self {
            commands: Vec::new(),
            numcmd: 0,
        }
    }

    pub fn with_default_options() -> Self {
        let mut ctx = Self::new();
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
            ctx.set_option(Smt2Option::Attribute(Attribute::new(String::from(o))));
        }
        ctx
    }

    pub fn merge(&mut self, mut other: Self) {
        self.numcmd += other.numcmd;
        self.commands.append(&mut other.commands);
    }

    pub fn add_command(&mut self, cmd: Smt2Command) -> &mut Self {
        self.commands.push(cmd);
        self
    }

    pub fn is_empty(&self) -> bool {
        self.commands.is_empty()
    }

    pub fn assert(&mut self, term: Term) -> &mut Self {
        self.commands.push(Smt2Command::Assert(term));
        self
    }

    pub fn check_sat(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::CheckSat);
        self
    }

    pub fn check_sat_assuming(&mut self, prop_literals: Vec<PropLiteral>) -> &mut Self {
        self.commands
            .push(Smt2Command::CheckSatAssuming(prop_literals));
        self
    }

    pub fn variable(&mut self, var_decl: VarDecl) -> &mut Self {
        self.commands.push(Smt2Command::Const(var_decl));
        self
    }

    pub fn datatype(&mut self, datatype: DataType) -> &mut Self {
        self.commands.push(Smt2Command::DataType(datatype));
        self
    }

    pub fn function(&mut self, function: Function) -> &mut Self {
        self.commands.push(Smt2Command::Function(function));
        self
    }

    pub fn constant(&mut self, ident: String, sort: String, term: Term) -> &mut Self {
        let mut f = Function::new(ident, sort);
        f.add_body(term);
        self.function(f)
    }

    pub fn sort(&mut self, sort: Sort) -> &mut Self {
        self.commands.push(Smt2Command::Sort(sort));
        self
    }

    pub fn echo(&mut self, message: String) -> &mut Self {
        self.commands.push(Smt2Command::Echo(message));
        self
    }

    pub fn exit(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::Exit);
        self
    }

    pub fn get_assertions(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::GetAssertions);
        self
    }

    pub fn get_assignment(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::GetAssignment);
        self
    }

    pub fn get_info(&mut self, info_flag: InfoFlag) -> &mut Self {
        self.commands.push(Smt2Command::GetInfo(info_flag));
        self
    }

    pub fn get_model(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::GetModel);
        self
    }

    pub fn get_option(&mut self, option: Smt2Option) -> &mut Self {
        self.commands.push(Smt2Command::GetOption(option));
        self
    }

    pub fn get_proof(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::GetProof);
        self
    }

    pub fn get_unsat_assumptions(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::GetUnsatAssumptions);
        self
    }

    pub fn get_unsat_core(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::GetUnsatCore);
        self
    }

    pub fn get_value(&mut self, expr: Vec<Term>) -> &mut Self {
        self.commands.push(Smt2Command::GetValue(expr));
        self
    }

    pub fn level(&mut self, smt2_context: Smt2Context) -> &mut Self {
        self.numcmd += smt2_context.numcmd;
        self.commands.push(Smt2Command::Level(smt2_context));
        self
    }

    pub fn reset(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::Reset);
        self
    }

    pub fn reset_assertions(&mut self) -> &mut Self {
        self.commands.push(Smt2Command::ResetAssertions);
        self
    }

    pub fn set_info(&mut self, info_flag: InfoFlag) -> &mut Self {
        self.commands.push(Smt2Command::SetInfo(info_flag));
        self
    }

    pub fn set_logic(&mut self, logic: String) -> &mut Self {
        self.commands.push(Smt2Command::SetLogic(logic));
        self
    }

    pub fn set_option(&mut self, option: Smt2Option) -> &mut Self {
        self.commands.push(Smt2Command::SetOption(option));
        self
    }

    pub fn section(&mut self, section: String) -> &mut Self {
        self.commands.push(Smt2Command::Section(section));
        self
    }

    pub fn subsection(&mut self, sub_section: String) -> &mut Self {
        self.commands.push(Smt2Command::SubSection(sub_section));
        self
    }

    pub fn comment(&mut self, comment: String) -> &mut Self {
        self.commands.push(Smt2Command::Comment(comment));
        self
    }

    pub fn raw(&mut self, raw: String) -> &mut Self {
        self.commands.push(Smt2Command::Raw(raw));
        self
    }

    // formats the current context into smtlib2 syntax
    pub fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        use Smt2Command::*;
        for cmd in &self.commands {
            match cmd {
                Assert(term) => {
                    write!(fmt, "(assert ")?;
                    if !fmt.compact() {
                        writeln!(fmt)?;
                    }
                    fmt.indent(|fmt| term.fmt(fmt))?;
                    if !fmt.compact() {
                        writeln!(fmt)?;
                    }
                    writeln!(fmt, ")")?;
                }
                CheckSat => writeln!(fmt, "(check-sat)")?,
                CheckSatAssuming(prop_literals) => {
                    write!(fmt, "(check-sat-assuming (")?;
                    for prop_literal in prop_literals {
                        prop_literal.fmt(fmt)?;
                        write!(fmt, " ")?;
                    }
                    writeln!(fmt, "))")?;
                }
                Const(var_decl) => var_decl.fmt(fmt)?,
                DataType(datatype) => datatype.fmt(fmt)?,
                Function(function) => function.fmt(fmt)?,
                Sort(sort) => sort.fmt(fmt)?,
                Echo(message) => writeln!(fmt, "(echo \"{message}\")")?,
                Exit => writeln!(fmt, "(exit)")?,
                GetAssertions => writeln!(fmt, "(get-assertions)")?,
                GetAssignment => writeln!(fmt, "(get-assignment)")?,
                GetInfo(info_flag) => {
                    write!(fmt, "(get-info ")?;
                    info_flag.fmt(fmt)?;
                    writeln!(fmt, ")")?;
                }
                GetModel => writeln!(fmt, "(get-model)")?,
                GetOption(option) => {
                    write!(fmt, "(get-option ")?;
                    option.fmt(fmt)?;
                    writeln!(fmt, ")")?;
                }
                GetProof => writeln!(fmt, "(get-proof)")?,
                GetUnsatAssumptions => writeln!(fmt, "(get-unsat-assumptions)")?,
                GetUnsatCore => writeln!(fmt, "(get-unsat-core)")?,
                GetValue(terms) => {
                    write!(fmt, "(get-value (")?;
                    for (i, t) in terms.iter().enumerate() {
                        if i != 0 {
                            write!(fmt, " ")?;
                        }
                        t.fmt(fmt)?;
                    }
                    writeln!(fmt, "))")?;
                }
                Level(smt2_context) => {
                    writeln!(fmt, "(push)")?;
                    smt2_context.fmt(fmt)?;
                    writeln!(fmt, "(pop)")?;
                }
                Reset => writeln!(fmt, "(reset)")?,
                ResetAssertions => writeln!(fmt, "(reset-assertions)")?,
                SetInfo(info_flag) => {
                    write!(fmt, "(set-info ")?;
                    info_flag.fmt(fmt)?;
                    writeln!(fmt, ")")?;
                }
                SetLogic(logic) => writeln!(fmt, "(set-logic {logic})")?,
                SetOption(option) => {
                    write!(fmt, "(set-option ")?;
                    option.fmt(fmt)?;
                    writeln!(fmt, ")")?;
                }
                Section(s) => {
                    if !fmt.compact() {
                        let sep = ";".repeat(100);
                        writeln!(fmt, "\n;{sep}\n; {s}\n;{sep}\n")?;
                    }
                }
                SubSection(s) => {
                    if !fmt.compact() {
                        let sep = "-".repeat(100);
                        writeln!(fmt, "\n; {s}\n;{sep}\n")?;
                    }
                }
                Comment(comment) => {
                    if !fmt.compact() {
                        writeln!(fmt, "; {comment}")?;
                    }
                }
                Raw(raw) => writeln!(fmt, "{raw}")?,
            }
        }
        Ok(())
    }

    /// returns a string of formatted SMT queries
    pub fn to_code(&self, compact: bool) -> String {
        let mut ret = String::with_capacity((self.commands.len() + self.numcmd) * 200);
        self.to_code_into(compact, &mut ret);
        ret
    }

    /// formats the SMT queries into the given string buffer
    pub fn to_code_into(&self, compact: bool, ret: &mut String) {
        let mut fmt = Formatter::new(ret, compact);
        self.fmt(&mut fmt).expect("formatting failed");
    }
}

impl fmt::Display for Smt2Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();
        self.fmt(&mut Formatter::new(&mut ret, false)).unwrap();
        write!(f, "{ret}")
    }
}

impl Default for Smt2Context {
    fn default() -> Self {
        Self::new()
    }
}
