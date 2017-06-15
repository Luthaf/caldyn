//! A simple Read-Eval-Print-Loop calculator, usable as a command line tool.
//!
//! usage:
//!    calc expr  # evaluate expr and print result to stdout
//!    calc       # start a REPL
//!
//! In the REPL mode, you can define variables with `<name> = <expr>`.

extern crate caldyn;
extern crate rustyline;
extern crate shellexpand;

use caldyn::Context;
use rustyline::Editor;
use std::io;
use std::io::prelude::*;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() > 1 {
        eval_args(&args[1..]);
    } else {
        repl()
    }
}

fn eval_args(args: &[String]) {
    let input = args.join(" ");
    match caldyn::eval(&input, None) {
        Ok(value) => println!("{}", value),
        Err(error) => {
            let _ = writeln!(io::stderr(), "{}", error);
        }
    }
}

fn repl() {
    let history_path = &shellexpand::tilde("~/.calcrs_history").into_owned();
    let mut editor = Editor::<()>::new();
    let _ = editor.load_history(history_path);
    let mut context = Context::new();
    loop {
        let line = editor.readline(">> ");
        match line {
            Ok(line) => {
                editor.add_history_entry(&line);
                if line.contains('=') {
                    add_variable(&mut context, &line);
                } else {
                    match caldyn::eval(&line, &context) {
                        Ok(value) => println!("{}", value),
                        Err(error) => {
                            let _ = writeln!(io::stderr(), "{}", error);
                        }
                    }
                }
            }
            Err(_) => break,
        }
    }
    let _ = editor.save_history(history_path);
}

fn add_variable(context: &mut Context, line: &str) {
    assert!(line.contains('='));
    let splitted = line.split('=').collect::<Vec<_>>();
    if splitted.len() != 2 {
        let _ = writeln!(io::stderr(), "error: too many = signs");
        return;
    }
    let var = splitted[0].trim();
    let value = splitted[1];
    if !caldyn::is_variable(var) {
        let _ = writeln!(io::stderr(), "error: '{}' is not a valid variable name", var);
        return;
    }
    match caldyn::eval(value, &*context) {
        Ok(value) => context.set(var, value),
        Err(error) => {
            let _ = writeln!(io::stderr(), "{}", error);
        }
    }
}
