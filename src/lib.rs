#![warn(missing_docs)]

//! Caldyn, a crate for dynamic evaluation of mathematical expressions.
//!
//! This crate provide run-time evaluation of mathematical expressions, embeded
//! in strings. The easyest way to use this crate is with the
//! [`eval`](fn.eval.html) function:
//!
//! ```
//! assert_eq!(caldyn::eval("3 + 5 * 2", None), Ok(13.0));
//! ```
//!
//! The second argument to `eval` is a [`Context`](struct.Context.html), that
//! can define variables:
//!
//! ```
//! use caldyn::Context;
//!
//! let mut context = Context::new();
//! context.set("a", 3.5);
//! assert_eq!(caldyn::eval("2 * a", &context), Ok(7.0));
//! ```
//!
//! It is also possible to separate the parsing from the evaluation of an
//! expression with the [`Expr`](struct.Expr.html) type. This allow to reuse
//! the same expression with different values for variables.
//!
//! ```
//! use caldyn::{Expr, Context};
//!
//! let expr = Expr::parse("3 + 5 * 2").unwrap();
//! assert_eq!(expr.eval(None), Ok(13.0));
//!
//! let expr = Expr::parse("3 / c + b").unwrap();
//! let mut context = Context::new();
//! context.set("c", 1.0);
//! context.set("b", 5.0);
//! assert_eq!(expr.eval(&context), Ok(8.0));
//!
//! context.set("b", 10.0);
//! assert_eq!(expr.eval(&context), Ok(13.0));
//! ```
//!
//! # Language definition
//!
//! The language implemented by caldyn can contain the following elements:
//!
//! - float litteral values: `-12.456`, `+0.0045e78`, ...;
//! - left and righ parenthesis;
//! - mathematical operators: `+` for addition, `-` for substraction,
//!   `*` for multiplication, `/` for division and `^` for exponentiation
//!   (`std::f64::powf`);
//! - variables. Variables names are ascii only, and can start by a letter or
//!   `_`, and can contain letters, digits or `_`.
//!
//! Any other symbol is forbidden in the input.
//!
//! The mathematical operators obey the usual relations of associativity and
//! precedence, but stil carry the floating point properties: addition is not
//! commutative, `NaN` and infinities exist, ...
//!
//! # Technical details
//!
//! caldyn is based on an AST interpreter, and uses a simple Shuntting-Yard
//! algorithm for parsing the expressions. It works only with `f64` data, and
//! perform a simple constant propagation to optimize the expressions.

mod error;
mod expr;
mod context;

pub use error::Error;
pub use expr::{Expr, eval};
pub use context::Context;
