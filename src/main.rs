#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

mod lib;

use rustyline::error::ReadlineError;
use rustyline::Editor;

use crate::lib::parser::Parser;
use crate::lib::types::{Ferr, Fexp};

static PROMPT: &'static str = "🦀λ> ";

fn run(input: &str) -> Result<Fexp, Ferr> {
    let mut ast = Parser::parse(input)?;
    Ok(ast)
}

fn main() {
    let mut rl = Editor::<()>::new();

    loop {
        let input = rl.readline(PROMPT);
        match input {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                match run(&line) {
                    Ok(o) => println!("{}", o.as_str()),
                    _ => panic!("BAD"),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
}
