//! Dev tool: translate ONE Solidity file through the frontend and print the result.
//!   cargo run -q -p sigil-frontends --example sol_translate -- <file.sol>
//! Prints `OK` + the emitted SIGIL on success, or `ERR <code> <message>` on a frontend reject.
//! (Companion to `sol_classify.rs`, which runs a whole corpus. Used to inspect a single flatten.)
use sigil_frontends::frontend_for;

fn main() {
    let path = match std::env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: sol_translate <file.sol>");
            std::process::exit(2);
        }
    };
    let src = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            std::process::exit(2);
        }
    };
    match frontend_for("solidity").unwrap().translate(&src, &path) {
        // `print!` (not `println!`): the emitted SIGIL already ends in a newline, so a `println!`
        // would append a spurious second one (which then leaks into any golden generated from this).
        Ok(e) => print!("OK\n{}", e.text),
        Err(d) => println!("ERR {} {}", d[0].code, d[0].message),
    }
}
