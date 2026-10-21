//! Every standard-library declaration file parses.

use std::fs;
use std::path::Path;

use flyscript::syntax::parse_declarations;

#[test]
fn std_declarations_parse() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("std");
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let source = fs::read_to_string(&path).unwrap();
        if let Err(d) = parse_declarations(&source) {
            panic!("{}", d.render(&path.display().to_string(), &source));
        }
    }
}
