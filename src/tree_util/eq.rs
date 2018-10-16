use id_tree::*;

/// Something `id_tree` is totally missing.
pub trait IdTreeEqExt<T, Rhs = Self>
where
    T: PartialEq<Rhs>,
{
    fn eq(&self, other: &Tree<Rhs>) -> bool;
    fn ne(&self, other: &Tree<Rhs>) -> bool {
        !self.eq(other)
    }
}

impl<T, Rhs> IdTreeEqExt<T, Rhs> for Tree<T>
where
    T: PartialEq<Rhs>,
{
    fn eq(&self, other: &Tree<Rhs>) -> bool {
        tree_equals(self, other)
    }
}

/// Test two `id_tree`s for equality.
pub fn tree_equals<L, R>(left: &Tree<L>, right: &Tree<R>) -> bool
where
    L: PartialEq<R>,
{
    match (left.root_node_id(), right.root_node_id()) {
        (Some(l), Some(r)) => tree_equals_result(left, l, right, r).unwrap_or(false),
        (None, None) => true,
        _ => false,
    }
}

fn tree_equals_result<L, R>(
    left: &Tree<L>,
    left_id: &NodeId,
    right: &Tree<R>,
    right_id: &NodeId,
) -> Result<bool, ()>
where
    L: PartialEq<R>,
{
    let left_node = left.get(left_id).or(Err(()))?;
    let right_node = right.get(right_id).or(Err(()))?;

    if left_node.data() != right_node.data() {
        return Ok(false);
    }

    let left_children = left_node.children();
    let right_children = right_node.children();

    for (left_child_id, right_child_id) in left_children.iter().zip(right_children.iter()) {
        if !tree_equals_result(left, left_child_id, right, right_child_id)? {
            return Ok(false);
        }
    }

    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_trees() {
        let left: Tree<()> = tree!();
        let right = tree!();

        assert!(left.eq(&right));
    }

    #[test]
    fn test_one_empty_tree() {
        let left = tree!();
        let right = tree!(1);

        assert!(left.ne(&right));
        assert!(right.ne(&left));
    }

    #[test]
    fn test_single_node_trees_eq() {
        let left = tree!(1);
        let right = tree!(1);

        assert!(left.eq(&right));
    }

    #[test]
    fn test_single_node_trees_ne() {
        let left = tree!(42);
        let right = tree!(37);

        assert!(left.ne(&right));
    }

    #[test]
    fn test_nested_trees_eq() {
        let left = tree!(1 => {2 => {3, 4}, 5 => {6,}, 7 => {}});
        let right = tree!(1 => {2 => {3, 4}, 5 => {6,}, 7 => {}});

        assert!(left.eq(&right));
    }

    #[test]
    fn test_nested_trees_structure_ne() {
        let left = tree!(1 => {2 => {3, 4}, 5 => {6,}, 7 => {}});
        let right = tree!(1 => {2 => {3}, 4 => {5, 6, 7}});

        assert!(left.ne(&right));
    }

    #[test]
    fn test_nested_trees_values_ne() {
        let left = tree!(1 => {2, 3 => {4}});
        let right = tree!(1 => {4, 2 => {3}});

        assert!(left.ne(&right));
    }

    #[test]
    fn test_different_types() {
        let left: Tree<String> = tree!("one".to_string() => {"two".to_string()});
        let right: Tree<&str> = tree!("tree" => {"four" => {"five"}});

        assert!(left.ne(&right));
    }
}
