# Rust SMT-LIB2

This library provides constructs to create [SMT-LIB2](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) ASTs that can be run in SMT solvers (e.g., Z3).

## License

see the LICENSE file.

## Authors

Reto Achermann


## Usage

Add `smt2` to your `Cargo.toml` file.

```rust
  // create a new SMT2 Context
  let mut smt = Smt2Context::new();

  let var = String::from("v");

  // declare a variable
  smt.variable(VarDecl::new(var.clone(), String::from("bv 64")));

  // assert
  smt.assert(Term::bveq(Term::ident(var.clone()), Term::num(3)));

  // check satisfiability
  smt.check_sat();

  // Generate and print the SMT2 code
  println!("{}", smt.to_code());
```