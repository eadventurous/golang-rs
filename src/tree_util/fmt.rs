use std::fmt::{Debug, Display, Error, Formatter, Result};

use id_tree::*;

pub struct TreeFmt<'a, T: 'a>(pub &'a Tree<T>);

type Style<T> = fn(&T, &mut Formatter) -> Result;

impl<'a, T> TreeFmt<'a, T> {
    fn outer(&self, f: &mut Formatter, style: Style<T>) -> Result {
        match self.0.root_node_id() {
            Some(node_id) => {
                writeln!(f, "Tree:")?;
                self.inner(f, node_id, 0, style)?;
            }
            None => write!(f, "Empty tree")?,
        }
        Ok(())
    }

    fn inner(&self, f: &mut Formatter, node_id: &NodeId, level: usize, style: Style<T>) -> Result {
        let tree = &self.0;
        let node = tree.get(node_id).or(Err(Error))?;

        for _ in 0..level {
            write!(f, "  ")?;
        }
        let tick = ['-', '+', '*'][level % 3];
        write!(f, "{} ", tick)?;

        style(node.data(), f)?;
        writeln!(f);

        for child in node.children().iter() {
            self.inner(f, child, level + 1, style)?;
        }
        Ok(())
    }
}

fn style_display<T: Display>(data: &T, f: &mut Formatter) -> Result {
    write!(f, "{}", data)
}

fn style_debug<T: Debug>(data: &T, f: &mut Formatter) -> Result {
    write!(f, "{:?}", data)
}

impl<'a, T: Display> Display for TreeFmt<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.outer(f, style_display)
    }
}

impl<'a, T: Debug> Debug for TreeFmt<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        self.outer(f, style_debug)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display() {
        let tree = tree!(1i32 => {2, 3 => {4 => {5}}, 6});
        let expected = "Tree:
- 1
  + 2
  + 3
    * 4
      - 5
  + 6
";
        assert_eq!(expected, format!("{}", TreeFmt(&tree)));
    }
}
