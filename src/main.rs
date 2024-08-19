use realistic::{RealProblem, Simple};
use std::io;

pub fn main() {
    let debug_parse = false;

    loop {
        let mut input = String::new();

        io::stdin()
            .read_line(&mut input)
            .expect("Failed to read calculator input");

        let expr = input.trim();
        if expr.is_empty() {
            break;
        }

        let expr: Simple = match expr.parse() {
            Ok(parsed) => parsed,
            Err(text) => {
                eprintln!("Parsing your input failed: {text}");
                continue;
            }
        };

        if debug_parse {
            eprintln!("expression parsed as: {expr:?}");
        }

        let ans = expr.evaluate();
        match ans {
            Ok(ans) => {
                if ans.is_whole() {
                    println!("{ans}");
                } else if ans.is_rational() {
                    if ans.prefer_fraction() {
                        println!("{ans} ~= {ans:#.10}");
                    } else {
                        println!("{ans} = {ans:#}");
                    }
                } else {
                    println!("{ans} ~= {ans:#.20}");
                }
            }
            Err(RealProblem::InsufficientParameters) => {
                println!("The operator needs more parameters")
            }
            Err(RealProblem::NotFound) => println!("Symbol not found"),
            Err(RealProblem::DivideByZero) => println!("Attempted division by zero"),
            _ => println!("Calculation failed: {ans:?}"),
        }
    }
}
