#![deny(clippy::all)]
#![warn(clippy::pedantic)]

pub use paste;

/// Generates a unique key for an item within a map in storage.
/// First it creates a prefix string with the module path, key identifier, and value identifier.
/// The final key is made up of the <prefix>.<key-type-instance-to-string>
#[macro_export]
macro_rules! map_key {
    ($k:ident, $v:ident) => {
        format!(
            "{}.{}",
            concat!(module_path!(), "::", stringify!($k), ":", stringify!($v)),
            $k
        )
        .as_bytes()
    };
}

/// A macro to generate functions for storing, retrieving, and optionally clearing a single item in storage.
/// Each item is identified by a unique key, and can be of various standard types like String and integers,
/// as well as custom types represented as strings, or integers.
/// The macro supports thread-local caching to optimize read operations.
/// It also automatically generates tests to ensure the functionality of the generated functions.
///
/// Usage:
/// item!(name: String) - Generates `set_name`, `clear_name`, and `name` functions for a String type.
/// item!(name!: String) - Similar to above but without `clear_name` & assumes the value is always set before get is called (non-optional).
/// item!(name: Type as String) - Handles custom types that are stored as Strings.
/// item!(name!: Type as String) - Non-optional version for custom types stored as Strings.
/// item!(name: u64) - For numeric types, here using u64 as an example.
/// item!(name!: u64) - Non-optional version for numeric types.
/// item!(name: Type as u64) - Custom types represented as numeric types.
/// item!(name!: Type as u64) - Non-optional version for custom types represented as numeric types.
#[macro_export]
macro_rules! item {
    ($i:ident: String) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<Option<String>>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _utf8>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: &str) {
                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some(Some($i.to_owned())));

                storage.set([<$i _key>](), $i.as_bytes())
            }

            #[allow(dead_code)]
            pub fn [<clear _ $i>](storage: &mut dyn ::cosmwasm_std::Storage) {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if cache_mut.is_some() {
                        *cache_mut = Some(None);
                    }

                    storage.remove([<$i _key>]())
                })
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> Option<String> {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = cache_mut.clone() {
                        return value;
                    }

                    let stored = storage
                        .get([<$i _key>]())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes");

                    *cache_mut = Some(stored.clone());

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get_clear>] {
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;
                use super::[<clear_ $i>] as clear;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {

                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage), None);

                    set(&mut storage, "test");

                    assert_eq!(get(&storage), Some("test".to_owned()));

                    assert_eq!(storage, MockStorage::from((key(), "test")));

                    clear(&mut storage);

                    assert_eq!(get(&storage), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($i:ident!: String) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<String>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _utf8>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: &str) {
                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some($i.to_owned()));
                storage.set([<$i _key>](), $i.as_bytes())
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> String {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = cache_mut.clone() {
                        return value;
                    }

                    let stored = storage
                        .get([<$i _key>]())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes")
                        .expect(concat!(stringify!($i), " always set"));

                    *cache_mut = Some(stored.clone());

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get>] {
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key(), "test"));

                    assert_eq!(get(&storage), "test");

                    set(&mut storage, "test-1");

                    assert_eq!(get(&storage), "test-1");

                    assert_eq!(storage, MockStorage::from((key(), "test-1")));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($i:ident: $t:path as String) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<Option<$t>>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _utf8>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: $t) {
                storage.set([<$i _key>](), $i.as_ref().as_bytes());

                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some(Some($i)));
            }

            #[allow(dead_code)]
            pub fn [<clear _ $i>](storage: &mut dyn ::cosmwasm_std::Storage) {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if cache_mut.is_some() {
                        *cache_mut = Some(None);
                    }

                    storage.remove([<$i _key>]())
                })
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> Option<$t> {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = cache_mut.clone() {
                        return value;
                    }

                    let stored = storage
                        .get([<$i _key>]())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes")
                        .map($t::from);

                    *cache_mut = Some(stored.clone());

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get_clear>] {
                use super::$t;
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;
                use super::[<clear_ $i>] as clear;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {
                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage), None);

                    set(&mut storage, $t::from("test"));

                    assert_eq!(get(&storage), Some($t::from("test")));

                    assert_eq!(storage, MockStorage::from((key(), "test")));

                    clear(&mut storage);

                    assert_eq!(get(&storage), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($i:ident!: $t:path as String) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<$t>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _utf8>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: $t) {
                storage.set([<$i _key>](), $i.as_ref().as_bytes());

                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some($i));
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> $t {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = cache_mut.clone() {
                        return value;
                    }

                    let stored = storage
                        .get([<$i _key>]())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes")
                        .map($t::from)
                        .expect(concat!(stringify!($i), " always set"));

                    *cache_mut = Some(stored.clone());

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get>] {
                use super::$t;
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key(), "test"));

                    assert_eq!(get(&storage), "test".into());

                    set(&mut storage, "test-1".into());

                    assert_eq!(get(&storage), "test-1".into());

                    assert_eq!(storage, MockStorage::from((key(), "test-1")));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($i:ident: $t:ty) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<Option<$t>>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _ $t _be>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: $t) {
                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some(Some($i)));

                storage.set([<$i _key>](), &$i.to_be_bytes())
            }

            #[allow(dead_code)]
            pub fn [<clear _ $i>](storage: &mut dyn ::cosmwasm_std::Storage) {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if cache_mut.is_some() {
                        *cache_mut = Some(None);
                    }

                    storage.remove([<$i _key>]())
                })
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> Option<$t> {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = cache_mut.clone() {
                        return value;
                    }

                    let stored = storage
                        .get([<$i _key>]())?
                        .try_into()
                        .map($t::from_be_bytes)
                        .map(Some)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($t)));

                    *cache_mut = Some(stored);

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get_clear>] {
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;
                use super::[<clear_ $i>] as clear;

                $crate::gen_int_mock_storage_impl!($t);

                #[test]
                fn works() {
                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage), None);

                    set(&mut storage, $t::MAX);

                    assert_eq!(get(&storage), Some($t::MAX));

                    assert_eq!(storage, MockStorage::from((key(), $t::MAX)));

                    clear(&mut storage);

                    assert_eq!(get(&storage), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($i:ident!: $t:ty) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<$t>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _ $t _be>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: $t) {
                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some($i));

                storage.set([<$i _key>](), &$i.to_be_bytes())
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> $t {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = *cache_mut {
                        return value;
                    }

                    let stored = storage
                        .get([<$i _key>]())
                        .expect(concat!(stringify!($i), " always set"))
                        .try_into()
                        .map($t::from_be_bytes)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($t)));

                    *cache_mut = Some(stored);

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get>] {
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;

                $crate::gen_int_mock_storage_impl!($t);

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key(), 1));

                    assert_eq!(get(&storage), 1);

                    set(&mut storage, 2);

                    assert_eq!(get(&storage), 2);

                    assert_eq!(storage, MockStorage::from((key(), 2)));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($i:ident: $t:path as $int:ty) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<Option<$int>>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _ $t _be>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: $t) {
                let int: $int = $i.into();

                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some(Some(int)));

                storage.set([<$i _key>](), &int.to_be_bytes())
            }

            #[allow(dead_code)]
            pub fn [<clear _ $i>](storage: &mut dyn ::cosmwasm_std::Storage) {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if cache_mut.is_some() {
                        *cache_mut = Some(None);
                    }

                    storage.remove([<$i _key>]())
                })
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> Option<$t> {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = *cache_mut {
                        return value.map($t::from);
                    }

                    let stored = storage
                        .get([<$i _key>]())?
                        .try_into()
                        .map($int::from_be_bytes)
                        .map($t::from)
                        .map(Some)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($t)));

                    *cache_mut = Some(stored.clone().map($int::from));

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get_clear>] {
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;
                use super::[<clear_ $i>] as clear;

                $crate::gen_int_mock_storage_impl!($int);

                #[test]
                fn works() {
                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage), None);

                    set(&mut storage, $int::MAX.into());

                    assert_eq!(get(&storage), Some($int::MAX.into()));

                    assert_eq!(storage, MockStorage::from((key(), $int::MAX.into())));

                    clear(&mut storage);

                    assert_eq!(get(&storage), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($i:ident!: $t:path as $int:ty) => {
        $crate::paste::paste! {
            ::std::thread_local! {
                static [<$i:upper _CACHE>]: ::std::cell::RefCell<Option<$int>> = ::std::cell::RefCell::new(None);
            }

            const fn [<$i _key>]() -> &'static [u8] {
                concat!(module_path!(), "::", stringify!([<$i _ $t _be>])).as_bytes()
            }

            pub fn [<set _ $i>](storage: &mut dyn ::cosmwasm_std::Storage, $i: $t) {
                let int: $int = $i.into();

                [<$i:upper _CACHE>].with(|cache| *cache.borrow_mut() = Some(int));

                storage.set([<$i _key>](), &int.to_be_bytes())
            }

            pub fn $i(storage: &dyn ::cosmwasm_std::Storage) -> $t {
                [<$i:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    if let Some(value) = *cache_mut {
                        return value.into();
                    }

                    let int = storage
                        .get([<$i _key>]())
                        .expect(concat!(stringify!($i), " always set"))
                        .try_into()
                        .map($int::from_be_bytes)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($t)));

                    *cache_mut = Some(int);

                    int.into()
                })
            }

            #[cfg(test)]
            mod [<test_ $i _set_get>] {
                use super::$t;
                use super::[<$i _key>] as key;
                use super::[<set_ $i>] as set;
                use super::[<$i>] as get;

                $crate::gen_int_mock_storage_impl!($int);

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key(), 1));

                    assert_eq!(get(&storage), 1.into());

                    set(&mut storage, 2.into());

                    assert_eq!(get(&storage), 2.into());

                    assert_eq!(storage, MockStorage::from((key(), 2)));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };
}

/// A macro to generate functions for storing, retrieving, and optionally clearing items in a map-like storage structure.
/// The map is keyed by a specified type, and values can be of various standard types like String and integers,
/// as well as custom types represented as strings or integers.
/// This macro supports thread-local caching for each key-value pair, optimizing read operations.
/// It also automatically generates tests to validate the functionality of the generated functions.
///
/// Usage:
/// map!(key:KeyType => value: String) - Generates `set_key_value`, `clear_key_value`, and `key_value` functions for String values.
/// map!(key:KeyType => value!: String) - Similar to above but without `clear_key_value` & assumes the value is always set before get is called (non-optional).
/// map!(key:KeyType => value: ``CustomType`` as String) - Custom types that are stored as Strings.
/// map!(key:KeyType => value!: ``CustomType`` as String) - Non-optional version for custom types stored as Strings.
/// map!(key:KeyType => value: u64) - For numeric values, here using u64 as an example.
/// map!(key:KeyType => value!: u64) - Non-optional version for numeric values.
/// map!(key:KeyType => value: ``CustomType`` as u64) - Custom types represented as numeric types.
/// map!(key:KeyType => value!: ``CustomType`` as u64) - Non-optional version for custom types represented as numeric types.
#[macro_export]
macro_rules! map {
    ($k:ident:$kt:ty => $v:ident: String) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, Option<String>>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }

            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([<$v _utf8>])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: &str) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), Some($v.to_owned())));
                storage.set([<$k _ $v _key>]($k).as_slice(), $v.as_bytes())
            }

            #[allow(dead_code)]
            pub fn [<clear _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), None));
                storage.remove([<$k _ $v _key>]($k).as_slice())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> Option<String> {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return value.clone();
                    }

                    let stored = storage
                        .get([<$k _ $v _key>]($k).as_slice())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes");

                    cache_mut.insert(cache_key, stored.clone());

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get_clear>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use [<clear_ $k _ $v>] as clear;
                use $crate::ExampleKey;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {
                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage, $kt::example()), None);

                    set(&mut storage, $kt::example(), "test");

                    assert_eq!(get(&storage, $kt::example()), Some("test".to_owned()));

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), "test")));

                    clear(&mut storage, $kt::example());

                    assert_eq!(get(&storage, $kt::example()), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($k:ident:$kt:ty => $v:ident!: String) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, String>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }


            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([<$v _utf8>])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: &str) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), $v.to_owned()));

                storage.set([<$k _ $v _key>]($k).as_slice(), $v.as_bytes())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> String {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return value.clone();
                    }

                    let stored = storage
                        .get([<$k _ $v _key>]($k).as_slice())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes")
                        .expect(concat!(stringify!([<$k _ $v>]), " always set"));

                    cache_mut.insert(cache_key, stored.clone());

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use $crate::ExampleKey;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key($kt::example()).as_slice(), "test"));

                    assert_eq!(get(&storage, $kt::example()), "test");

                    set(&mut storage, $kt::example(), "test-1");

                    assert_eq!(get(&storage, $kt::example()), "test-1");

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), "test-1")));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($k:ident:$kt:ty => $v:ident: $vt:path as String) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, Option<String>>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }

            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([<$v _utf8>])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: &str) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), Some($v.to_owned())));

                storage.set([<$k _ $v _key>]($k).as_slice(), $v.as_bytes())
            }

            #[allow(dead_code)]
            pub fn [<clear _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), None));

                storage.remove([<$k _ $v _key>]($k).as_slice())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> Option<$vt> {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return value.clone().map($vt::from);
                    }

                    let maybe_stored_string = storage
                        .get([<$k _ $v _key>]($k).as_slice())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes");

                    cache_mut.insert(cache_key, maybe_stored_string.clone());

                    maybe_stored_string.map($vt::from)
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get_clear>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use [<clear_ $k _ $v>] as clear;
                use $crate::ExampleKey;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {
                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage, $kt::example()), None);

                    set(&mut storage, $kt::example(), "test");

                    assert_eq!(get(&storage, $kt::example()), Some("test".to_owned().into()));

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), "test")));

                    clear(&mut storage, $kt::example());

                    assert_eq!(get(&storage, $kt::example()), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($k:ident:$kt:ty => $v:ident!: $vt:path as String) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, String>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }

            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([<$v _utf8>])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: &str) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), $v.to_owned()));

                storage.set([<$k _ $v _key>]($k).as_slice(), $v.as_bytes())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> $vt {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return value.clone().into()
                    }

                    let stored_string = storage
                        .get([<$k _ $v _key>]($k).as_slice())
                        .map(String::from_utf8)
                        .transpose()
                        .expect("a valid utf-8 sequence of bytes")
                        .expect(concat!(stringify!([<$k _ $v>]), " always set"));

                    cache_mut.insert(cache_key, stored_string.clone());

                    stored_string.into()
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use $crate::ExampleKey;

                $crate::gen_string_mock_storage_impl!();

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key($kt::example()).as_slice(), "test"));

                    assert_eq!(get(&storage, $kt::example()), "test".to_owned().into());

                    set(&mut storage, $kt::example(), "test-1");

                    assert_eq!(get(&storage, $kt::example()), "test-1".to_owned().into());

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), "test-1")));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($k:ident:$kt:ty => $v:ident: $int:ty) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, Option<$int>>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }

            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([[<$v _ $int _be>]])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: $int) {
                let int: $int = $v.into();

                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), Some(int)));

                storage.set([<$k _ $v _key>]($k).as_slice(), int.to_be_bytes().as_slice())
            }

            #[allow(dead_code)]
            pub fn [<clear _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), None));

                storage.remove([<$k _ $v _key>]($k).as_slice())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> Option<$int> {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return value.clone();
                    }

                    let Some(bytes) = storage.get([<$k _ $v _key>]($k).as_slice()) else {
                        cache_mut.insert(cache_key, None);
                        return None;
                    };

                    let stored = bytes
                        .try_into()
                        .map($int::from_be_bytes)
                        .map(Some)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($int)));

                    cache_mut.insert(cache_key, stored);

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get_clear>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use [<clear_ $k _ $v>] as clear;
                use $crate::ExampleKey;

                $crate::gen_int_mock_storage_impl!($int);

                #[test]
                fn works() {
                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage, $kt::example()), None);

                    set(&mut storage, $kt::example(), $int::MAX);

                    assert_eq!(get(&storage, $kt::example()), Some($int::MAX));

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), $int::MAX)));

                    clear(&mut storage, $kt::example());

                    assert_eq!(get(&storage, $kt::example()), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($k:ident:$kt:ty => $v:ident!: $int:ty) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, $int>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }

            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([[<$v _ $int _be>]])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: $int) {
                let int: $int = $v.into();

                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), int));

                storage.set([<$k _ $v _key>]($k).as_slice(), int.to_be_bytes().as_slice())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> $int {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return *value;
                    }

                    let stored = storage
                        .get([<$k _ $v _key>]($k).as_slice())
                        .expect(concat!(stringify!([<$k _ $v>]), " always set"))
                        .try_into()
                        .map($int::from_be_bytes)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($int)));

                    cache_mut.insert(cache_key, stored);

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use $crate::ExampleKey;

                $crate::gen_int_mock_storage_impl!($int);

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key($kt::example()).as_slice(), 1));

                    assert_eq!(get(&storage, $kt::example()), 1);

                    set(&mut storage, $kt::example(), 2);

                    assert_eq!(get(&storage, $kt::example()), 2);

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), 2)));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($k:ident:$kt:ty => $v:ident: $vt:path as $int:ty) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, Option<$int>>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }

            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([[<$v _ $int _be>]])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: $vt) {
                let int: $int = $v.into();

                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), Some(int)));

                storage.set([<$k _ $v _key>]($k).as_slice(), int.to_be_bytes().as_slice())
            }

            #[allow(dead_code)]
            pub fn [<clear _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt) {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), None));

                storage.remove([<$k _ $v _key>]($k).as_slice())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> Option<$vt> {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return value.map($vt::from);
                    }

                    let Some(bytes) = storage.get([<$k _ $v _key>]($k).as_slice()) else {
                        cache_mut.insert(cache_key, None);
                        return None;
                    };

                    let stored = bytes
                        .try_into()
                        .map($int::from_be_bytes)
                        .map($vt::from)
                        .map(Some)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($int)));

                    cache_mut.insert(cache_key, stored.map(Into::into));

                    stored
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get_clear>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use [<clear_ $k _ $v>] as clear;
                use $crate::ExampleKey;

                $crate::gen_int_mock_storage_impl!($int);

                #[test]
                fn works() {
                    let mut storage = MockStorage::default();

                    assert_eq!(get(&storage, $kt::example()), None);

                    set(&mut storage, $kt::example(), $int::MAX.into());

                    assert_eq!(get(&storage, $kt::example()), Some($int::MAX.into()));

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), $int::MAX)));

                    clear(&mut storage, $kt::example());

                    assert_eq!(get(&storage, $kt::example()), None);

                    assert_eq!(storage, MockStorage::default());

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };

    ($k:ident:$kt:ty => $v:ident!: $vt:path as $int:ty) => {
        $crate::paste::paste! {
            std::thread_local! {
                static [<$k:upper _ $v:upper _CACHE>]: ::std::cell::RefCell<::std::collections::HashMap<String, $int>> =
                ::std::cell::RefCell::new(::std::collections::HashMap::default());
            }

            fn [<$k _ $v _key>](key: $kt) -> Vec<u8> {
                format!(
                    "{}.{}",
                    concat!(module_path!(), "::", stringify!($k), ":", stringify!([[<$v _ $int _be>]])),
                    key
                )
                .into_bytes()
            }

            pub fn [<set _ $k _ $v>](storage: &mut dyn ::cosmwasm_std::Storage, $k: $kt, $v: $vt) {
                let int: $int = $v.into();

                [<$k:upper _ $v:upper _CACHE>].with(|cache| cache.borrow_mut().insert($k.to_string(), int));

                storage.set([<$k _ $v _key>]($k).as_slice(), int.to_be_bytes().as_slice())
            }

            pub fn [<$k _ $v>](storage: &dyn ::cosmwasm_std::Storage, $k: $kt) -> $vt {
                [<$k:upper _ $v:upper _CACHE>].with(|cache| {
                    let mut cache_mut = cache.borrow_mut();

                    let cache_key = $k.to_string();

                    if let Some(value) = cache_mut.get(&cache_key) {
                        return $vt::from(*value);
                    }

                    let int = storage
                        .get([<$k _ $v _key>]($k).as_slice())
                        .expect(concat!(stringify!([<$k _ $v>]), " always set"))
                        .try_into()
                        .map($int::from_be_bytes)
                        .expect(concat!("the exact amount of bytes in a ", stringify!($int)));

                    cache_mut.insert(cache_key, int);

                    int.into()
                })
            }

            #[cfg(test)]
            mod [<test_ $k _ $v _set_get>] {
                use super::*;
                use [<$k _ $v _key>] as key;
                use [<set_ $k _ $v>] as set;
                use [<$k _ $v>] as get;
                use $crate::ExampleKey;

                $crate::gen_int_mock_storage_impl!($int);

                #[test]
                fn works() {
                    let mut storage = MockStorage::from((key($kt::example()).as_slice(), 1));

                    assert_eq!(get(&storage, $kt::example()), 1.into());

                    set(&mut storage, $kt::example(), 2.into());

                    assert_eq!(get(&storage, $kt::example()), 2.into());

                    assert_eq!(storage, MockStorage::from((key($kt::example()).as_slice(), 2)));

                    assert_eq!(storage.read_count(), 1);
                }
            }
        }
    };
}

/// `ExampleKey` is a trait for generating example keys for testing.
pub trait ExampleKey: Sized {
    /// Returns an example instance of the implementing type.
    fn example() -> Self;
}

/// A macro for implementing the `ExampleKey` trait.
/// It enables easy specification of example keys for different types,
#[macro_export]
macro_rules! example_key {
    ($t:ty, $example:expr) => {
        #[cfg(test)]
        impl $crate::ExampleKey for $t {
            fn example() -> $t {
                <$t>::from($example)
            }
        }
    };
}

macro_rules! impl_int_example_key {
    ($($int:ty),+) => {
        $(
            impl ExampleKey for $int {
                fn example() -> $int {
                    <$int>::MAX
                }
            }
        )+
    }
}

impl_int_example_key!(u8, u16, u32, u64, u128);

impl ExampleKey for String {
    fn example() -> String {
        "test".to_owned()
    }
}

#[macro_export]
macro_rules! gen_string_mock_storage_impl {
    () => {
        #[derive(Default, Debug)]
        struct MockStorage {
            read_count: ::std::cell::RefCell<usize>,
            key: Option<String>,
            value: Option<String>,
        }

        impl MockStorage {
            fn read_count(&self) -> usize {
                *self.read_count.borrow()
            }
        }

        impl PartialEq for MockStorage {
            fn eq(&self, other: &Self) -> bool {
                self.key.eq(&other.key) && self.value.eq(&other.value)
            }
        }

        impl<V: ToString> From<(&[u8], V)> for MockStorage {
            fn from((key, value): (&[u8], V)) -> Self {
                Self {
                    key: Some(String::from_utf8(key.into()).unwrap()),
                    value: Some(value.to_string()),
                    ..Self::default()
                }
            }
        }

        impl ::cosmwasm_std::Storage for MockStorage {
            fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
                let value = self.value.clone().map(String::into_bytes);

                if value.is_some() {
                    assert_eq!(self.key.as_ref().map(String::as_bytes).unwrap(), key);
                }

                *self.read_count.borrow_mut() += 1;

                value
            }

            fn range<'a>(
                &'a self,
                _start: Option<&[u8]>,
                _end: Option<&[u8]>,
                _order: cosmwasm_std::Order,
            ) -> Box<dyn Iterator<Item = cosmwasm_std::Record> + 'a> {
                unimplemented!()
            }

            fn set(&mut self, key: &[u8], value: &[u8]) {
                if self.key.is_some() {
                    assert_eq!(self.key.as_ref().map(String::as_bytes).unwrap(), key);
                }

                self.key = Some(String::from_utf8(key.into()).unwrap());
                self.value = Some(String::from_utf8(value.into()).unwrap());
            }

            fn remove(&mut self, key: &[u8]) {
                if self.key.is_some() {
                    assert_eq!(self.key.as_ref().map(String::as_bytes).unwrap(), key);
                }
                self.key = None;
                self.value = None;
            }
        }
    };
}

#[macro_export]
macro_rules! gen_int_mock_storage_impl {
    ($int:ty) => {
        #[derive(Default, Debug)]
        struct MockStorage {
            read_count: ::std::cell::RefCell<usize>,
            key: Option<String>,
            value: Option<$int>,
        }

        impl MockStorage {
            fn read_count(&self) -> usize {
                *self.read_count.borrow()
            }
        }

        impl PartialEq for MockStorage {
            fn eq(&self, other: &Self) -> bool {
                self.key.eq(&other.key) && self.value.eq(&other.value)
            }
        }

        impl From<(&[u8], $int)> for MockStorage {
            fn from((key, value): (&[u8], $int)) -> Self {
                Self {
                    key: Some(String::from_utf8(key.into()).unwrap()),
                    value: Some(value),
                    ..Self::default()
                }
            }
        }

        impl ::cosmwasm_std::Storage for MockStorage {
            fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
                let value = self.value.map(<$int>::to_be_bytes).map(|b| b.to_vec());

                if value.is_some() {
                    assert_eq!(self.key.as_ref().map(String::as_bytes).unwrap(), key);
                }

                *self.read_count.borrow_mut() += 1;

                value
            }

            fn range<'a>(
                &'a self,
                _start: Option<&[u8]>,
                _end: Option<&[u8]>,
                _order: cosmwasm_std::Order,
            ) -> Box<dyn Iterator<Item = cosmwasm_std::Record> + 'a> {
                unimplemented!()
            }

            fn set(&mut self, key: &[u8], value: &[u8]) {
                if self.key.is_some() {
                    assert_eq!(self.key.as_ref().map(String::as_bytes).unwrap(), key);
                }

                self.key = Some(String::from_utf8(key.into()).unwrap());
                self.value = Some(value.try_into().map(<$int>::from_be_bytes).unwrap());
            }

            fn remove(&mut self, key: &[u8]) {
                if self.key.is_some() {
                    assert_eq!(self.key.as_ref().map(String::as_bytes).unwrap(), key);
                }
                self.key = None;
                self.value = None;
            }
        }
    };
}
