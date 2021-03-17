use std::any::{type_name, Any, TypeId};
use std::collections::BTreeMap;

#[derive(Debug)]
pub struct Converter {
    converts: BTreeMap<(TypeId, TypeId), Box<dyn Any>>,
    named_converts: BTreeMap<(String, TypeId, TypeId), Box<dyn Any>>,
    defaults: BTreeMap<TypeId, Box<dyn Any>>,
    named_defaults: BTreeMap<(String, TypeId), Box<dyn Any>>,
}

impl Converter {
    // Create a new converter
    pub fn new() -> Self {
        Self {
            converts: BTreeMap::new(),
            named_converts: BTreeMap::new(),
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
    pub fn add_as<From: Sized + Any, To: Sized + Any>(&mut self, name: &str, f: fn(&Self, From) -> To) {
        let type_ids = (name.to_string(), TypeId::of::<From>(), TypeId::of::<To>());
        self.named_converts.insert(type_ids, Box::new(f));
    }

    // Define default value for type T
    pub fn def<T: Sized + Any + Clone>(&mut self, value: T) {
        let type_id = TypeId::of::<T>();
        self.defaults.insert(type_id, Box::new(value));
    }

    // Defined named default value for type T
    pub fn def_as<T: Sized + Any + Clone>(&mut self, name: &str, value: T) {
        let type_id = TypeId::of::<T>();
        self.named_defaults.insert((name.to_string(),type_id), Box::new(value));
    }

    // Apply conversion from From into To
    pub fn convert<From: Sized + Any, To: Sized + Any>(&self, x: From) -> To {
        match self.get::<From, To>() {
            Some(f) => f(x),
            None => panic!(
                "Undefined conversion from {:?} to {:?}",
                type_name::<From>(),
                type_name::<To>()
            ),
        }
    }

    // Apply named conversion from From into To
    pub fn convert_as<From: Sized + Any, To: Sized + Any>(&self, name: &str, x: From) -> To {
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
    pub fn default<T: Sized + Any + Clone>(&self) -> T {
        match self.get_default::<T>() {
            Some(v) => v,
            None => panic!(
                "Undefined default for {:?}",
                type_name::<T>(),
            ),
        }
    }    

    // Generate named default value of type T
    pub fn default_as<T: Sized + Any + Clone>(&self, name: &str) -> T {
        match self.get_default_as::<T>(name) {
            Some(v) => v,
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

    pub fn get_as<From: Sized + Any, To: Sized + Any>(&self, name: &str) -> Option<Box<dyn Fn(From) -> To + '_>> {
        let type_ids = (name.to_string(), TypeId::of::<From>(), TypeId::of::<To>());
        self.named_converts.get(&type_ids).and_then(|f| {
            f.downcast_ref::<fn(&Self, From) -> To>()
                .and_then(|f| Some(Box::new(move |x: From| f(&self, x)) as Box<dyn Fn(From) -> To>))
        })
    }

    pub fn get_default<T: Sized + Any + Clone>(&self) -> Option<T> {
        let type_id = TypeId::of::<T>();
        self.defaults.get(&type_id)
            .and_then(|f|f.downcast_ref::<T>())
            .map(|v| v.clone())
    }

    pub fn get_default_as<T: Sized + Any + Clone>(&self, name: &str) -> Option<T> {
        let type_id = TypeId::of::<T>();
        self.named_defaults.get(&(name.to_string(), type_id))
            .and_then(|f|f.downcast_ref::<T>())
            .map(|v| v.clone())
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
        let mut c = Converter::new();
        c.def(0u64);
        c.add(|_, name: String| Provider { name: name, id: 0 });
        c.add(|c, name: String| Chain {
            name: name.clone(),
            id: c.default_as("id"),
            default_provider: c.convert(name),
        });
        c.add(|c, b: AbstractBlock| Block {
            chain: c.convert(b.chain),
            height: b.height,
            id: c.default(),
            provider: c.convert(b.provider),
        });

        let a_block = AbstractBlock {
            chain: "chain1".to_string(),
            height: 1,
            provider: "provider2".to_string(),
        };

        let block: Block = c.convert(a_block);

        let expected = Block {
            chain: Chain {
                name: "chain1".to_string(),
                id: 0,
                default_provider: Provider {
                    name: "chain1".to_string(),
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

        //assert_eq!(block, expected);

        println!("{:?}", block)
    }
}
