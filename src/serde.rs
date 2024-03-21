// Copyright (c) 2016 multimap developers
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

//! Serde trait implementations for MultiMap

extern crate serde;

use alloc::fmt;
use core::marker::PhantomData;

use self::serde::de::{MapAccess, Visitor};
use self::serde::{Deserialize, Deserializer, Serialize, Serializer};

use BTreeMultiMap;

impl<K, V> Serialize for BTreeMultiMap<K, V>
where
    K: Serialize + Ord,
    V: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<K, V> BTreeMultiMapVisitor<K, V>
where
    K: Ord,
{
    fn new() -> Self {
        BTreeMultiMapVisitor {
            marker: PhantomData,
        }
    }
}

struct BTreeMultiMapVisitor<K, V> {
    marker: PhantomData<BTreeMultiMap<K, V>>,
}

impl<'a, K, V> Visitor<'a> for BTreeMultiMapVisitor<K, V>
where
    K: Deserialize<'a> + Ord,
    V: Deserialize<'a>,
{
    type Value = BTreeMultiMap<K, V>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("expected a map")
    }

    fn visit_map<M>(self, mut visitor: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'a>,
    {
        let mut values = BTreeMultiMap::new();

        while let Some((key, value)) = visitor.next_entry()? {
            values.inner.insert(key, value);
        }

        Ok(values)
    }
}

impl<'a, K, V> Deserialize<'a> for BTreeMultiMap<K, V>
where
    K: Deserialize<'a> + Ord,
    V: Deserialize<'a>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'a>,
    {
        deserializer.deserialize_map(BTreeMultiMapVisitor::<K, V>::new())
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {

    extern crate serde_test;

    use self::serde_test::{assert_tokens, Token};

    use super::*;

    #[test]
    fn test_empty() {
        let map = BTreeMultiMap::<char, u8>::new();

        assert_tokens(&map, &[Token::Map { len: Some(0) }, Token::MapEnd]);
    }

    #[test]
    fn test_single() {
        let mut map = BTreeMultiMap::<char, u8>::new();
        map.insert('x', 1);

        assert_tokens(
            &map,
            &[
                Token::Map { len: Some(1) },
                Token::Char('x'),
                Token::Seq { len: Some(1) },
                Token::U8(1),
                Token::SeqEnd,
                Token::MapEnd,
            ],
        );
    }

    #[test]
    fn test_multiple() {
        let mut map = BTreeMultiMap::<char, u8>::new();
        map.insert('x', 1);
        map.insert('x', 3);
        map.insert('x', 1);
        map.insert('x', 5);

        assert_tokens(
            &map,
            &[
                Token::Map { len: Some(1) },
                Token::Char('x'),
                Token::Seq { len: Some(4) },
                Token::U8(1),
                Token::U8(3),
                Token::U8(1),
                Token::U8(5),
                Token::SeqEnd,
                Token::MapEnd,
            ],
        );
    }
}
