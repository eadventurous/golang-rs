use super::*;

use std::ffi::OsStr;
use std::fs::{self, DirEntry};
use std::path::{Path, PathBuf};

pub fn base() -> &'static Path {
    Path::new("src/syn/golang/tests/sources")
}

fn files(dir: &str) -> impl Iterator<Item = PathBuf> {
    fs::read_dir(base().join(dir))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry: &DirEntry| entry.path().extension() == Some(OsStr::new("go")))
        .map(|entry: DirEntry| entry.path())
}

fn load_tree_from<P: AsRef<Path>>(path: P) -> Result<Tree<String>, String> {
    let code = ::std::fs::read_to_string(path.as_ref()).unwrap();
    let tree = build_tree(&code, path.as_ref().to_str().unwrap().to_owned(), false);
    tree
}

#[test]
fn test_ok() {
    for file in files("ok") {
        let tree = load_tree_from(&file);
        assert!(
            tree.is_ok(),
            "File {:?} must be Ok:\n{}",
            file.file_name().unwrap(),
            tree.err().unwrap()
        );
    }
}

#[test]
fn test_err() {
    for file in files("err") {
        let tree = load_tree_from(&file);
        assert!(
            tree.is_err(),
            "File {:?} must be Err:\n{}",
            file.file_name().unwrap(),
            TreeFmt(&tree.unwrap())
        );
    }
}

/// Use it to debug some particular files.
#[test]
fn print_tree() {
    let filenames: &[&str] = &[];
    for file in filenames
        .into_iter()
        .map(|filename| base().join("ok").join(filename))
    {
        let tree = load_tree_from(&file).unwrap();
        println!("{:?}", file.file_name().unwrap());
        println!("{}", TreeFmt(&tree));
    }
}
