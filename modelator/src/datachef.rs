use std::any::{type_name, Any, TypeId};
use std::collections::BTreeMap;

/// Recipe describes how a set of data structures can be produced from
/// the set of ingredients (other data structures).
/// It attempts to solve the problem of conversion between data structures
/// that arises often especially during testing, when concrete structures
/// need to be produced from the abstract ones and vice versa.
/// 
/// # Example
///
/// Imagine your application processes phone records, which it receives
/// from another system, and needs to check them for structural correctness.
/// The records could look like that:
/// ```
/// pub struct Record {
///     pub name: String,
///     pub address: Address,
///     pub landline: Phone,
///     pub mobile: Phone,
/// }

/// pub struct Address {
///     pub postal_code: u32,
///     pub city: String,
///     pub street: String,
///     pub door: u32,
/// }

/// pub struct Phone {
///     pub area_code: u32,
///     pub number: u32,
/// }
/// ```
///
/// And the checking function could look like that:
/// ```
/// fn check_record(r: Record) -> bool {
///     // Name is not too short or too long
///     r.name.len() >= 6 &&
///     r.name.len() <= 100 &&
///     // Postal code is 5 digits
///     r.address.postal_code >= 10000 &&
///     r.address.postal_code <= 99999 &&
///     // Phone codes are 3 digits
///     r.landline.area_code >= 100 &&
///     r.landline.area_code <= 999 &&
///     r.mobile.area_code >= 100 &&
///     r.mobile.area_code <= 999
///     // ...
/// }
/// ```
///
/// Now, the question is how do you prepare tests for this function?
/// You could of course each time create concrete records:
/// ```
/// let record = Record {
///     name: "John Smith".to_string(),
///     address: Address {
///         ...
///     },
///     landline: Phone {
///         area_code: 123,
///         number: 456789,
///     },
///     mobile: ...,
/// }
/// ```
/// The problem with that approach is that it is too verbose and inflexible.
/// It can be simplified somehow by introducing local variables (dummies),
/// but using dummies is also quite ad-hoc and inflexible,
/// Our data chef recommends you to define a recipe instead!
///
/// ```
/// let mut r = Recipe::new();
/// // default phone
/// r.put(|_| Phone {
///     area_code: 123,
///     number: 456789,
/// });
/// // default address
/// r.put(|_| Address {
///     postal_code: 10179,
///     city: "Berlin".to_string(),
///     street: "Molkenmarkt".to_string(),
///     door: 1,
/// });
/// // a recipe to produce `Record` from a name, using default address and phones
/// r.add(|r, name: String| Record {
///     name,
///     address: r.take(),
///     landline: r.take(),
///     mobile: r.take(),
/// });
/// ```
/// In the recipe above you define (put on the table) default values
/// for `Phone` and `Address`, and define a simple recipe to make (prepare)
/// a `Record` from a name, using defaults for other fields.
/// With that recipe we can already test `check_record()`:
/// ```
/// assert!(check_record(r.make("John Smith".to_string())));
/// assert!(!check_record(r.make("short".repeat(1))));
/// assert!(!check_record(r.make("long".repeat(100))));
/// ```
/// Now, what if we want to test how the phones are handled?
/// Add more recipes to cook phones!
/// ```
/// // Recipe for cooking a phone out of a code and a number
/// r.add(|_, phone: (u32, u32)| Phone {
///     area_code: phone.0,
///     number: phone.1,
/// });
/// // Recipe for cooking a record with the landline number provided,
/// // and defaults for the rest of the fields.
/// r.add(|r, phone: (u32, u32)| Record {
///     name: "John Smith".to_string(),
///     address: r.take(),
///     landline: r.make(phone),
///     mobile: r.take(),
/// });
///
/// // A generic test for phones: the phone being tested 
/// // depends on what the recipe produces from the code and the number.
/// let test_phone = |r: &Recipe| {
///     assert!(check_record(r.make((123u32,1234567u32))));
///     assert!(!check_record(r.make((1u32,1234567u32))));
///     assert!(!check_record(r.make((1234u32,1234567u32))));
/// };
/// test_phone(&r); // tests landline phone
/// 
/// // Redefine the recipe to generate a mobile phone 
/// r.add(|r, phone: (u32, u32)| Record {
///     name: "John Smith".to_string(),
///     address: r.take(),
///     landline: r.take(),
///     mobile: r.make(phone),
/// });
/// test_phone(&r); // tests mobile phone
/// ```

#[derive(Debug)]
pub struct Recipe {
    converts: BTreeMap<(TypeId, TypeId), Box<dyn Any>>,
    named_converts: BTreeMap<(String, TypeId, TypeId), Box<dyn Any>>,

    // TODO get rid of those by redirecting default -> convert with From == ()
    defaults: BTreeMap<TypeId, Box<dyn Any>>,
    named_defaults: BTreeMap<(String, TypeId), Box<dyn Any>>,
}

impl Recipe {
    /// Create a new recipe
    pub fn new() -> Self {
        Self {
            converts: BTreeMap::new(),
            named_converts: BTreeMap::new(),

            // TODO: get rid of those by instead redirecting default -> convert with From == ()
            defaults: BTreeMap::new(),
            named_defaults: BTreeMap::new(),
        }
    }

    /// Add conversion from From into To.
    /// Use [make()](Recipe::make) to apply the conversion.
    pub fn add<From, To>(&mut self, converter: fn(&Self, From) -> To)
    where
        From: Sized + Any,
        To: Sized + Any,
    {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        self.converts.insert(type_ids, Box::new(converter));
    }

    /// Add named conversion from From into To.
    /// Use [make_as()](Recipe::make_as) to apply the conversion.
    pub fn add_as<From, To>(&mut self, name: &str, converter: fn(&Self, From) -> To)
    where
        From: Sized + Any,
        To: Sized + Any,
    {
        let type_ids = (name.to_string(), TypeId::of::<From>(), TypeId::of::<To>());
        self.named_converts.insert(type_ids, Box::new(converter));
    }

    /// Put default value for type T.
    /// Use [take()](Recipe::take) to retrieve the default.
    pub fn put<T: Sized + Any>(&mut self, default: fn(&Self) -> T) {
        let type_id = TypeId::of::<T>();
        self.defaults.insert(type_id, Box::new(default));
    }

    /// Put named default value for type T.
    /// Use [take_as()](Recipe::take_as) to retrieve the default.
    pub fn put_as<T: Sized + Any>(&mut self, name: &str, f: fn(&Self) -> T) {
        let type_id = TypeId::of::<T>();
        self.named_defaults
            .insert((name.to_string(), type_id), Box::new(f));
    }

    /// Makes from From a To, applying a previously defined conversion.
    pub fn make<From, To>(&self, x: From) -> To
    where
        From: Sized + Any,
        To: Sized + Any,
    {
        match self.get::<From, To>() {
            Some(f) => f(x),
            None => panic!(
                "Undefined conversion from {:?} to {:?}",
                type_name::<From>(),
                type_name::<To>()
            ),
        }
    }

    /// Makes from From a To, applying a previously defined named conversion
    pub fn make_as<From, To>(&self, name: &str, x: From) -> To
    where
        From: Sized + Any,
        To: Sized + Any,
    {
        match self.get_as::<From, To>(name) {
            Some(f) => f(x),
            None => panic!(
                "Undefined conversion named '{}' from {:?} to {:?}",
                name,
                type_name::<From>(),
                type_name::<To>()
            ),
        }
    }

    /// Take default value of type T.
    pub fn take<T: Sized + Any>(&self) -> T {
        match self.get_default::<T>() {
            Some(f) => f(),
            None => panic!("Undefined default for {:?}", type_name::<T>(),),
        }
    }

    /// Take named default value of type T.
    pub fn take_as<T: Sized + Any>(&self, name: &str) -> T {
        match self.get_default_as::<T>(name) {
            Some(f) => f(),
            None => panic!(
                "Undefined default named '{}' for {:?}",
                name,
                type_name::<T>(),
            ),
        }
    }

    fn get<From, To>(&self) -> Option<Box<dyn Fn(From) -> To + '_>>
    where
        From: Sized + Any,
        To: Sized + Any,
    {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        self.converts.get(&type_ids).and_then(|f| {
            f.downcast_ref::<fn(&Self, From) -> To>()
                .and_then(|f| Some(Box::new(move |x: From| f(&self, x)) as Box<dyn Fn(From) -> To>))
        })
    }

    fn get_as<From, To>(&self, name: &str) -> Option<Box<dyn Fn(From) -> To + '_>>
    where
        From: Sized + Any,
        To: Sized + Any,
    {
        let type_ids = (name.to_string(), TypeId::of::<From>(), TypeId::of::<To>());
        self.named_converts.get(&type_ids).and_then(|f| {
            f.downcast_ref::<fn(&Self, From) -> To>()
                .and_then(|f| Some(Box::new(move |x: From| f(&self, x)) as Box<dyn Fn(From) -> To>))
        })
    }

    fn get_default<T: Sized + Any>(&self) -> Option<Box<dyn Fn() -> T + '_>> {
        let type_id = TypeId::of::<T>();
        self.defaults.get(&type_id).and_then(|f| {
            f.downcast_ref::<fn(&Self) -> T>()
                .and_then(|f| Some(Box::new(move || f(&self)) as Box<dyn Fn() -> T>))
        })
    }

    fn get_default_as<T: Sized + Any>(&self, name: &str) -> Option<Box<dyn Fn() -> T + '_>> {
        let type_id = TypeId::of::<T>();
        self.named_defaults
            .get(&(name.to_string(), type_id))
            .and_then(|f| {
                f.downcast_ref::<fn(&Self) -> T>()
                    .and_then(|f| Some(Box::new(move || f(&self)) as Box<dyn Fn() -> T>))
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub struct Record {
        pub name: String,
        pub address: Address,
        pub landline: Phone,
        pub mobile: Phone,
    }

    pub struct Address {
        pub postal_code: u32,
        pub city: String,
        pub street: String,
        pub door: u32,
    }

    pub struct Phone {
        pub area_code: u32,
        pub number: u32,
    }

    fn check_record(r: Record) -> bool {
        // Name is not too short or too long
        r.name.len() >= 6 &&
        r.name.len() <= 100 &&
        // Postal code is 5 digits
        r.address.postal_code >= 10000 &&
        r.address.postal_code <= 99999 &&
        // Phone codes are 3 digits
        r.landline.area_code >= 100 &&
        r.landline.area_code <= 999 &&
        r.mobile.area_code >= 100 &&
        r.mobile.area_code <= 999
        // ...
    }

    #[test]
    fn test_check_record() {
        let mut r = Recipe::new();
        r.put(|_| Phone {
            area_code: 123,
            number: 456789,
        });
        r.put(|_| Address {
            postal_code: 10179,
            city: "Berlin".to_string(),
            street: "Molkenmarkt".to_string(),
            door: 1,
        });
        r.add(|r, name: String| Record {
            name,
            address: r.take(),
            landline: r.take(),
            mobile: r.take(),
        });
 
        assert!(check_record(r.make("John Smith".to_string())));
        assert!(!check_record(r.make("short".repeat(1))));
        assert!(!check_record(r.make("long".repeat(100))));

        r.add(|_, phone: (u32, u32)| Phone {
            area_code: phone.0,
            number: phone.1,
        });
        r.add(|r, phone: (u32, u32)| Record {
            name: "John Smith".to_string(),
            address: r.take(),
            landline: r.make(phone),
            mobile: r.take(),
        });

        let test_phone = |r: &Recipe| {
            assert!(check_record(r.make((123u32,1234567u32))));
            assert!(!check_record(r.make((1u32,1234567u32))));
            assert!(!check_record(r.make((1234u32,1234567u32))));
        };
        test_phone(&r);
        r.add(|r, phone: (u32, u32)| Record {
            name: "John Smith".to_string(),
            address: r.take(),
            landline: r.take(),
            mobile: r.make(phone),
        });
        test_phone(&r);
    }


    #[derive(Debug, PartialEq)]
    pub struct Chain {
        name: String,
        id: u64,
        default_provider: Provider,
    }

    #[derive(Debug, PartialEq)]
    pub struct Provider {
        name: String,
        id: u64,
    }

    #[derive(Debug, PartialEq)]
    pub struct Block {
        chain: Chain,
        height: u64,
        id: u64,
        provider: Provider,
    }

    #[derive(Debug, PartialEq)]
    pub struct AbstractBlock {
        chain: String,
        height: u64,
        provider: String,
    }

    #[test]
    pub fn test() {
        let mut r = Recipe::new();
        r.put_as("height", |_| 1u64);
        r.put_as("id", |_| 0u64);
        r.put(|r| Provider {
            name: "default_provider".to_string(),
            id: r.take_as("id"),
        });
        r.add(|r, name: String| Provider {
            name: name,
            id: r.take_as("id"),
        });
        r.add(|r, name: String| Chain {
            name: name.clone(),
            id: r.take_as("id"),
            default_provider: r.take(),
        });
        r.add(|r, b: AbstractBlock| Block {
            chain: r.make(b.chain),
            height: b.height,
            id: r.take_as("id"),
            provider: r.make(b.provider),
        });

        let a_block = AbstractBlock {
            chain: "chain1".to_string(),
            height: 1,
            provider: "provider2".to_string(),
        };

        let block: Block = r.make(a_block);

        let expected = Block {
            chain: Chain {
                name: "chain1".to_string(),
                id: 0,
                default_provider: Provider {
                    name: "default_provider".to_string(),
                    id: 0,
                },
            },
            height: 1,
            id: 0,
            provider: Provider {
                name: "provider2".to_string(),
                id: 0,
            },
        };

        assert_eq!(block, expected);
    }
}
