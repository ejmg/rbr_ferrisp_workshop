#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

mod parser;
mod types;

use rustyline::error::ReadlineError;
use rustyline::Editor;

static PROMPT: &'static str = "🦀λ> ";

fn main() {
    let mut rl = Editor::<()>::new();

    loop {
        let input = rl.readline(PROMPT);
        match input {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                print!("Input: {}", line);
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
