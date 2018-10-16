#![macro_use]

/// Construct HashSet literal as `hash_set!{a, b, c}`.
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

#[cfg(test)]
mod test {
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
}
