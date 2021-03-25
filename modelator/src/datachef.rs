use std::any::{type_name, Any, TypeId};
use std::collections::BTreeMap;

#[derive(Debug)]
pub struct Recipe {
    converts: BTreeMap<(TypeId, TypeId), Box<dyn Any>>,
    named_converts: BTreeMap<(String, TypeId, TypeId), Box<dyn Any>>,

    // TODO get rid of those by redirecting default -> convert with From == ()
    defaults: BTreeMap<TypeId, Box<dyn Any>>,
    named_defaults: BTreeMap<(String, TypeId), Box<dyn Any>>,
}

impl Recipe {
    // Create a new converter
    pub fn new() -> Self {
        Self {
            converts: BTreeMap::new(),
            named_converts: BTreeMap::new(),

            // TODO: get rid of those by instead redirecting default -> convert with From == ()
            defaults: BTreeMap::new(),
            named_defaults: BTreeMap::new(),
        }
    }

    // Add conversion from From into To
    pub fn add<From: Sized + Any, To: Sized + Any>(&mut self, f: fn(&Self, From) -> To) {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        self.converts.insert(type_ids, Box::new(f));
    }

    // Add named conversion from From into To
    pub fn add_as<From: Sized + Any, To: Sized + Any>(
        &mut self,
        name: &str,
        f: fn(&Self, From) -> To,
    ) {
        let type_ids = (name.to_string(), TypeId::of::<From>(), TypeId::of::<To>());
        self.named_converts.insert(type_ids, Box::new(f));
    }

    // Define default value for type T
    pub fn def<T: Sized + Any>(&mut self, f: fn(&Self) -> T) {
        let type_id = TypeId::of::<T>();
        self.defaults.insert(type_id, Box::new(f));
    }

    // Defined named default value for type T
    pub fn def_as<T: Sized + Any>(&mut self, name: &str, f: fn(&Self) -> T) {
        let type_id = TypeId::of::<T>();
        self.named_defaults
            .insert((name.to_string(), type_id), Box::new(f));
    }

    pub fn cook<From: Sized + Any, To: Sized + Any>(&self, x: From) -> To {
        match self.get::<From, To>() {
            Some(f) => f(x),
            None => panic!(
                "Undefined conversion from {:?} to {:?}",
                type_name::<From>(),
                type_name::<To>()
            ),
        }
    }

    pub fn cook_as<From: Sized + Any, To: Sized + Any>(&self, name: &str, x: From) -> To {
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

    // Generate default value of type T
    pub fn take<T: Sized + Any>(&self) -> T {
        match self.get_default::<T>() {
            Some(f) => f(),
            None => panic!("Undefined default for {:?}", type_name::<T>(),),
        }
    }

    // Generate named default value of type T
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

    pub fn get<From: Sized + Any, To: Sized + Any>(&self) -> Option<Box<dyn Fn(From) -> To + '_>> {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        self.converts.get(&type_ids).and_then(|f| {
            f.downcast_ref::<fn(&Self, From) -> To>()
                .and_then(|f| Some(Box::new(move |x: From| f(&self, x)) as Box<dyn Fn(From) -> To>))
        })
    }

    pub fn get_as<From: Sized + Any, To: Sized + Any>(
        &self,
        name: &str,
    ) -> Option<Box<dyn Fn(From) -> To + '_>> {
        let type_ids = (name.to_string(), TypeId::of::<From>(), TypeId::of::<To>());
        self.named_converts.get(&type_ids).and_then(|f| {
            f.downcast_ref::<fn(&Self, From) -> To>()
                .and_then(|f| Some(Box::new(move |x: From| f(&self, x)) as Box<dyn Fn(From) -> To>))
        })
    }

    pub fn get_default<T: Sized + Any>(&self) -> Option<Box<dyn Fn() -> T + '_>> {
        let type_id = TypeId::of::<T>();
        self.defaults.get(&type_id).and_then(|f| {
            f.downcast_ref::<fn(&Self) -> T>()
                .and_then(|f| Some(Box::new(move || f(&self)) as Box<dyn Fn() -> T>))
        })
    }

    pub fn get_default_as<T: Sized + Any>(&self, name: &str) -> Option<Box<dyn Fn() -> T + '_>> {
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
        let mut c = Recipe::new();
        c.def_as("height", |_| 1u64);
        c.def_as("id", |_| 0u64);
        c.def(|c| Provider {
            name: "default_provider".to_string(),
            id: c.take_as("id"),
        });
        c.add(|c, name: String| Provider {
            name: name,
            id: c.take_as("id"),
        });
        c.add(|c, name: String| Chain {
            name: name.clone(),
            id: c.take_as("id"),
            default_provider: c.take(),
        });
        c.add(|c, b: AbstractBlock| Block {
            chain: c.cook(b.chain),
            height: b.height,
            id: c.take_as("id"),
            provider: c.cook(b.provider),
        });

        let a_block = AbstractBlock {
            chain: "chain1".to_string(),
            height: 1,
            provider: "provider2".to_string(),
        };

        let block: Block = c.cook(a_block);

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
