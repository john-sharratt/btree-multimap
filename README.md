# Multimap implementation for Rust

This is a sorted multimap implementation with range support for Rust. Implemented as a thin wrapper around
std::collections::BTreeMap.

## Example

````rust
extern crate multimap;

use btreemultimap::BTreeMultiMap;

fn main () {
    let mut map = BTreeMultiMap::new();
    map.insert(3, "a");
    map.insert(5, "b");
    map.insert(5, "c");
    map.insert(8, "c");
    map.insert(9, "d");

    assert_eq!(map[3], "a");
    assert_eq!(map.get(5), Some(&"b"));
    assert_eq!(map.get_vec(5), Some(&vec!["b", "c"]));

    for (&key, &value) in map.range((Included(&4), Included(&8))) {
        println!("{}: {}", key, value);
    }
    
    let mut iter = map.range(4..=8);
    assert_eq!(Some((&5, &"b")), iter.next());
    assert_eq!(Some((&5, &"c")), iter.next());
    assert_eq!(Some((&8, &"c")), iter.next());
    assert_eq!(None, iter.next());
}
````

## License

Licensed under either of
 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
