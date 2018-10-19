#![macro_use]

/// Construct HashSet literal as `hash_set!{a, b, c}`.
#[macro_export]
macro_rules! hash_set {
    ($($k: expr),*) => {{
        let mut set = ::std::collections::hash_set::HashSet::new();
        $( set.insert($k); )*
        set
    }};
    ($($k: expr,)*) => {
        hash_set!($($k),*)
    }
}

/// Construct HashMap literal as `hash_map!{k1: v1, k2: v2}`.
#[macro_export]
macro_rules! hash_map {
    ($($k: expr, $v: expr),*) => {{
        let mut map = ::std::collections::hash_map::HashMap::new();
        $( map.insert($k, $v); )*
        map
    }};
    ($($k: expr, $v: expr,)*) => {{
        hash_map!($($k, $v),*)
    }}
}

/// Constantly return `x` no matter what argument(s) passed to lambda.
/// Prepend number of expected arguments if more than one.
///
/// # Note
///
/// This requires `x` to be `Clone`able for repeated usage (e.g. to
/// cast into `Fn` trait instead of `FnOnce`)
#[macro_export]
macro_rules! constant {
    ($x:expr) => {
        move |_| $x
    };
    (1, $x:expr) => {
        move |_| $x
    };
    (2, $x:expr) => {
        move |_, _| $x
    };
    (3, $x:expr) => {
        move |_, _, _| $x
    };
    (4, $x:expr) => {
        move |_, _, _, _| $x
    };
}

/// Tree literals with [`id_tree`] crate and `tree!` macro with ease!
///
/// # Examples
///
/// Empty tree:
/// ```
/// tree!();
/// ```
///
/// Tree of one element:
/// ```
/// tree!("root");
/// ```
///
/// Same as above, no children:
/// ```
/// tree!("root" => {});
/// ```
///
/// Root element has only one children:
/// ```
/// tree!("root" => {"child"});
/// ```
///
/// Root element has multiple children:
/// ```
/// tree!("root" => {"one", "four", "two"});
/// ```
///
/// Tree of height 4:
/// ```
/// tree!("parent" => {"daughter", "son" => {"grandson", "granddaughter"}});
/// ```
///
/// General pattern:
/// ```bnf
/// <Nodes> ::= ( <Node> "," )*
/// <Node> ::= <Value> <Children>
/// <Children> ::= "=>" "{" <Nodes> "}" | ""
/// ```
///
/// [`id_tree`]: https://crates.io/crates/id_tree
#[macro_export]
macro_rules! tree {
    () => (
        ::id_tree::TreeBuilder::new().build()
    );
    ($root:expr) => {{
        use id_tree::*;

        ::id_tree::TreeBuilder::new().with_root(Node::new($root)).build()
    }};
    ($root:expr => { $($children:tt)* }) => {{
        let mut tree = tree!($root);
        {
            let root_node = tree.root_node_id().unwrap().clone();
            tree!(@ tree, root_node, $($children)*);
        }
        tree
    }};

    // # Private implementation

    // empty base case
    // `let _ =` used to suppress 'unused' warning.
    (@ $tree:expr, $parent:expr) => {{ let _ = $parent; }};
    (@ $tree:expr, $parent:expr,) => {{ let _ = $parent; }};

    // one-child base case
    (@ $tree:expr, $parent:expr, $child:expr) => (
        $tree.insert(Node::new($child), ::id_tree::InsertBehavior::UnderNode(&$parent)).unwrap()
    );

    // parent=>children base case
    (@ $tree:expr, $parent:expr, $child:expr => { $($grandchildren:tt)* }) => {{
        let new_parent = tree!(@ $tree, $parent, $child);
        tree!(@ $tree, new_parent, $($grandchildren)*);
    }};

    // comma-separated recursive case
    (@ $tree:expr, $parent:expr, $child:expr, $($rest:tt)*) => {{
        tree!(@ $tree, $parent, $child);
        tree!(@ $tree, $parent, $($rest)*);
    }};

    // parent=>children recursive case
    (@ $tree:expr, $parent:expr, $child:expr => { $($grandchildren:tt)* }, $($rest:tt)*) => {
        tree!(@ $tree, $parent, $child => { $($grandchildren)* });
        tree!(@ $tree, $parent, $($rest)*);
    };
}

#[cfg(test)]
mod test {
    use id_tree::*;
    use std::collections::HashMap;
    use std::collections::HashSet;

    #[test]
    fn test_hash_set() {
        // no trailing comma
        let full: HashSet<u32> = hash_set! {1, 2, 3};
        assert_eq!(3, full.len());

        // trailing comma
        let _comma: HashSet<u32> = hash_set! {1, 2, 3,};

        let empty: HashSet<u32> = hash_set!{};
        assert!(empty.is_empty());
    }

    #[test]
    fn test_hash_map() {
        let full: HashMap<&'static str, u32> = hash_map! {
            "apples", 0xdeadbeef,
            "oranges", 1337,  // trailing comma
        };
        assert_eq!(2, full.len());

        let _comma: HashMap<&'static str, u32> = hash_map! {
            "apples", 0xdeadbeef,
            "oranges", 1337  // no trailing comma
        };

        let empty: HashMap<u32, ()> = hash_map!{};
        assert!(empty.is_empty());
    }

    #[test]
    fn test_constant() {
        let x = constant!(42);

        assert_eq!(42, x(0));
        assert_eq!(42, x(1337));
    }

    #[test]
    fn test_constant_many() {
        let xs = constant!(2, "42");

        assert_eq!("42", xs(3.14, vec![false]));
        assert_eq!("42", xs(0.0, vec![]));

        let xs = constant!(3, "42");

        assert_eq!("42", xs('x', "y", String::from("z")));
        assert_eq!("42", xs('\0', "", Default::default()));

        let xs = constant!(4, "42");

        assert_eq!("42", xs(1, 2, 3, 4));
        assert_eq!("42", xs(5, 6, 7, 8));
    }

    #[test]
    fn test_tree_empty() {
        let _tree: Tree<i32> = tree!();
    }

    #[test]
    fn test_tree_single_root() {
        let _tree: Tree<i32> = tree!(42);
    }

    #[test]
    fn test_tree_without_children() {
        let _tree: Tree<i32> = tree!(42 => {});
    }

    #[test]
    fn test_tree_with_children() {
        let tree: Tree<i32> = tree!(42 => {37, 99});

        let mut nodes = tree
            .traverse_pre_order(tree.root_node_id().unwrap())
            .unwrap();
        assert_eq!(&42, nodes.next().unwrap().data());
        assert_eq!(&37, nodes.next().unwrap().data());
        assert_eq!(&99, nodes.next().unwrap().data());
        assert!(nodes.next().is_none());
    }

    #[test]
    fn test_tree_with_children_nested() {
        let tree: Tree<i32> = tree!(42 => {37, 99 => {25}, 80 => {9001, 1337}, 0 => {}});

        let pre_order = vec![42, 37, 99, 25, 80, 9001, 1337, 0];
        let nodes = tree
            .traverse_pre_order(tree.root_node_id().unwrap())
            .unwrap()
            .map(Node::data)
            .map(Clone::clone)
            .collect::<Vec<_>>();
        assert_eq!(pre_order, nodes);
    }

    #[test]
    #[cfg(skip)]
    fn test_tt_macro() {
        macro_rules! tt {
            () => {println!("tt(empty)")};
            ($node:expr) => {println!("tt(node).")};
            ($node:expr, $($rest:tt)*) => {
                print!("tt(node) and... ");
                tt!($($rest)*);
            };
            ($key:expr => $value:expr) => {
                println!("tt(key({}) => value({})).", $key, $value);
            };
            ($key:expr => $value:expr, $($rest:tt)*) => {
                print!("tt(key({}) => value({})) and... ", $key, $value);
                tt!($($rest)*);
            }
        }

        tt!();
        tt!(42);
        tt!('a' => 'b');
        tt!('a' => 'b');
        tt!('a' => 'b', 'c', 'd' => 'e');
    }
}
