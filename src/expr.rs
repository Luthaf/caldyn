use std::str::Chars;
use std::iter::Peekable;
use std::ascii::AsciiExt;

use error::Error;

enum Ast {
    Variable(String),
    Value(f64),
    Add(Box<Ast>, Box<Ast>),
    Sub(Box<Ast>, Box<Ast>),
    Mul(Box<Ast>, Box<Ast>),
    Div(Box<Ast>, Box<Ast>),
    Exp(Box<Ast>, Box<Ast>),
}

impl Ast {
    fn from_tokens(tokens: &mut Vec<Token>, context: &str) -> Result<Ast, Error> {
        match tokens.pop() {
            None => Err(Error::ParseError(format!("empty expression{}", context))),
            Some(token) => match token {
                Token::Value(value) => {
                    if let Ok(number) = value.parse() {
                        Ok(Ast::Value(number))
                    } else if is_ident(&value) {
                        Ok(Ast::Variable(value))
                    } else {
                        Err(Error::ParseError(format!("invalid value {}", value)))
                    }
                }
                Token::Op(op) => {
                    let right = Box::new(try!(Ast::from_tokens(tokens, " after operator")));
                    let left = Box::new(try!(Ast::from_tokens(tokens, " befor operator")));
                    match op {
                        Op::Plus => Ok(Ast::Add(left, right)),
                        Op::Minus => Ok(Ast::Sub(left, right)),
                        Op::Mul => Ok(Ast::Mul(left, right)),
                        Op::Div => Ok(Ast::Div(left, right)),
                        Op::Exp => Ok(Ast::Exp(left, right)),
                    }
                },
                _ => panic!("Internal error: got {:?} token after shunting yard"),
            }
        }
    }

    fn eval(&self) -> Result<f64, Error> {
        match *self {
            Ast::Variable(ref name) => Err(Error::NameError(format!("name '{}' is not defined", name))),
            Ast::Value(number) => Ok(number),
            Ast::Add(ref left, ref right) => Ok(try!(left.eval()) + try!(right.eval())),
            Ast::Sub(ref left, ref right) => Ok(try!(left.eval()) - try!(right.eval())),
            Ast::Mul(ref left, ref right) => Ok(try!(left.eval()) * try!(right.eval())),
            Ast::Div(ref left, ref right) => Ok(try!(left.eval()) / try!(right.eval())),
            Ast::Exp(ref left, ref right) => Ok(try!(left.eval()).powf(try!(right.eval()))),
        }
    }

    fn value(&self) -> Option<f64> {
        if let Ast::Value(value) = *self {
            Some(value)
        } else {
            None
        }
    }

    fn optimize(self) -> Ast {
        match self {
            Ast::Variable(_) | Ast::Value(_) => self,
            Ast::Add(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Ast::Value(left + right);
                    }
                }
                return Ast::Add(Box::new(left), Box::new(right));
            }
            Ast::Sub(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Ast::Value(left - right);
                    }
                }
                return Ast::Sub(Box::new(left), Box::new(right));
            }
            Ast::Mul(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Ast::Value(left * right);
                    }
                }
                return Ast::Mul(Box::new(left), Box::new(right));
            }
            Ast::Div(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Ast::Value(left / right);
                    }
                }
                return Ast::Div(Box::new(left), Box::new(right));
            }
            Ast::Exp(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Ast::Value(left.powf(right));
                    }
                }
                return Ast::Exp(Box::new(left), Box::new(right));
            }
        }
    }
}

pub struct Expr {
    ast: Ast,
}

impl Expr {
    pub fn parse(expression: &str) -> Result<Expr, Error> {
        let mut parser = Parser::new(expression);
        let mut output = Vec::new();
        let mut operators = Vec::new();

        'tokens: while let Some(token) = try!(parser.next()) {
            match token {
                Token::Value(_) => output.push(token),
                Token::Op(o1) => {
                    'operators: while let Some(token) = operators.last().cloned() {
                        match token {
                            Token::Op(o2) => {
                                if o1.is_left_associative() && o1.precedence() <= o2.precedence() {
                                    operators.pop();
                                    output.push(Token::Op(o2));
                                } else if o1.is_right_associative() && o1.precedence() < o2.precedence() {
                                    operators.pop();
                                    output.push(Token::Op(o2));
                                } else {
                                    break 'operators;
                                }
                            }
                            _ => break 'operators,
                        }
                    }
                    operators.push(token)
                }
                Token::LParen => operators.push(token),
                Token::RParen => {
                    while let Some(token) = operators.pop() {
                        match token {
                            Token::LParen => continue 'tokens,
                            Token::Op(_) => output.push(token),
                            other => panic!("Internal bug: found {:?} in operators stack", other)
                        }
                    }
                    return Err(Error::ParseError("mismatched parenthesis".into()))
                }
            }
        }

        while let Some(token) = operators.pop() {
            match token {
                Token::LParen => return Err(Error::ParseError("mismatched parenthesis".into())),
                Token::Op(_) => output.push(token),
                other => panic!("Internal bug: found {:?} in operators stack", other)
            }
        }

        let ast = try!(Ast::from_tokens(&mut output, ""));
        if output.is_empty() {
            Ok(Expr{ast: ast.optimize()})
        } else {
            Err(Error::ParseError("extra data at the end of the expression".into()))
        }
    }

    pub fn eval(&self) -> Result<f64, Error> {
        self.ast.eval()
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Op {
    Plus,
    Minus,
    Mul,
    Div,
    Exp,
}

impl Op {
    fn precedence(&self) -> u8 {
        match *self {
            Op::Plus => 1,
            Op::Minus => 1,
            Op::Mul => 2,
            Op::Div => 2,
            Op::Exp => 3,
        }
    }

    fn is_left_associative(&self) -> bool {
        match *self {
            Op::Plus => true,
            Op::Minus => true,
            Op::Mul => true,
            Op::Div => true,
            Op::Exp => false,
        }
    }

    fn is_right_associative(&self) -> bool {
        !self.is_left_associative()
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Value(String),
    Op(Op),
    LParen,
    RParen,
}


struct Parser<'a> {
    input: Peekable<Chars<'a>>,
}

impl<'a> Parser<'a> {
    fn new(string: &str) -> Parser {
        Parser {
            input: string.chars().peekable()
        }
    }

    fn next(&mut self) -> Result<Option<Token>, Error> {
        if let Some(c) = self.input.next() {
            let token = match c {
                ' ' | '\t' | '\n' | '\r' => return self.next(),
                c if is_value_start(c) => {
                    let mut ident = String::new();
                    ident.push(c);
                    'value: while let Some(&c) = self.input.peek() {
                        if is_value_part(c) {
                            self.input.next();
                            ident.push(c);
                        } else {
                            break 'value;
                        }
                    }
                    // Special case to handle numbers starting with + or -
                    if ident == "+" {
                        Token::Op(Op::Plus)
                    } else if ident == "-" {
                        Token::Op(Op::Minus)
                    } else {
                        Token::Value(ident)
                    }
                }
                '*' => Token::Op(Op::Mul),
                '/' => Token::Op(Op::Div),
                '^' => Token::Op(Op::Exp),
                '(' => Token::LParen,
                ')' => Token::RParen,
                other => return Err(Error::ParseError(format!("unexpected characted in input: {}", other)))
            };
            Ok(Some(token))
        } else {
            Ok(None)
        }
    }
}

fn is_value_start(c: char) -> bool {
    c == '+' || c == '-' || c.is_digit(10) || is_ident_start(c)
}

fn is_value_part(c: char) -> bool {
    c == '+' || c == '-' || is_ident_part(c)
}

fn is_ident_start(c: char) -> bool {
    c == '_' || (c.is_ascii() && c.is_alphabetic())
}

fn is_ident_part(c: char) -> bool {
    c == '_' || (c.is_ascii() && c.is_alphanumeric())
}

fn is_ident(ident: &str) -> bool {
    let mut chars = ident.chars();
    // Check first char
    if !chars.next().map_or(false, is_ident_start) {
        return false;
    }
    // Check all others
    for c in chars {
        if !is_ident_part(c) {
            return false;
        }
    }
    return true;
}

pub fn eval(input: &str) -> Result<f64, Error> {
    Expr::parse(input).and_then(|expr| expr.eval())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn idents() {
        assert!(is_ident_start('c'));
        assert!(is_ident_start('Z'));
        assert!(is_ident_start('_'));
        assert!(is_ident_start('f'));

        assert!(!is_ident_start('3'));
        assert!(!is_ident_start('à'));
        assert!(!is_ident_start('@'));

        assert!(is_ident_part('c'));
        assert!(is_ident_part('Z'));
        assert!(is_ident_part('_'));
        assert!(is_ident_part('f'));
        assert!(is_ident_part('3'));

        assert!(!is_ident_part('à'));
        assert!(!is_ident_part('@'));

        assert!(is_ident("_______"));
        assert!(is_ident("abc"));
        assert!(is_ident("a__45__bc"));
        assert!(!is_ident("a-bc"));
        assert!(!is_ident("@bc"));
        assert!(!is_ident("6bc"));
    }

    #[test]
    fn values() {
        assert!(is_value_start('c'));
        assert!(is_value_start('Z'));
        assert!(is_value_start('_'));
        assert!(is_value_start('f'));
        assert!(is_value_start('3'));
        assert!(is_value_start('+'));
        assert!(is_value_start('-'));

        assert!(!is_value_start('à'));
        assert!(!is_value_start('@'));

        assert!(is_value_part('c'));
        assert!(is_value_part('Z'));
        assert!(is_value_part('_'));
        assert!(is_value_part('f'));
        assert!(is_value_part('3'));
        assert!(is_value_part('-'));
        assert!(is_value_part('+'));

        assert!(!is_value_part('à'));
        assert!(!is_value_part('@'));
    }

    #[test]
    fn parse() {
        assert!(Expr::parse("3 + 5").is_ok());
        assert!(Expr::parse("(3 + 5)*45").is_ok());
        assert!(Expr::parse("(3 + 5)*\t\n45").is_ok());
        assert!(Expr::parse("(3 + 5^5e-6)*45").is_ok());
    }

    #[test]
    fn eval() {
        assert_eq!(super::eval("3 + 5"), Ok(8.0));
        assert_eq!(super::eval("2 - 5"), Ok(-3.0));
        assert_eq!(super::eval("2 * 5"), Ok(10.0));
        assert_eq!(super::eval("10 / 5"), Ok(2.0));
        assert_eq!(super::eval("2 ^ 3"), Ok(8.0));
        assert_eq!(super::eval("-3"), Ok(-3.0));
        assert_eq!(super::eval("25 + -3"), Ok(22.0));
        assert_eq!(super::eval("25 - -3"), Ok(28.0));
        assert_eq!(super::eval("25 - -3"), Ok(28.0));
        assert_eq!(super::eval("3 + 5 * 2"), Ok(13.0));
    }

    #[test]
    fn optimize() {
        let Expr{ast} = Expr::parse("3 + 5").unwrap();
        assert_eq!(ast.value(), Some(8.0));

        let Expr{ast} = Expr::parse("(3 + 5^2)*45").unwrap();
        assert_eq!(ast.value(), Some(1260.0));
    }
}
