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
}
