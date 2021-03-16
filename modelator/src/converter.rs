use std::any::{type_name, Any, TypeId};
use std::collections::BTreeMap;

pub struct Converter {
    converts: BTreeMap<(TypeId, TypeId), Box<dyn Any>>,
}

impl Converter {
    pub fn new() -> Self {
        Self {
            converts: BTreeMap::new(),
        }
    }

    pub fn add<From: Sized + Any, To: Sized + Any>(&mut self, f: fn(&Self, From) -> To) {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        self.converts.insert(type_ids, Box::new(f));
    }

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

    pub fn get<From: Sized + Any, To: Sized + Any>(&self) -> Option<Box<dyn Fn(From) -> To + '_>> {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        self.converts.get(&type_ids).and_then(|f| {
            f.downcast_ref::<fn(&Self, From) -> To>()
                .and_then(|f| Some(Box::new(move |x: From| f(&self, x)) as Box<dyn Fn(From) -> To>))
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
        let mut c = Converter::new();
        c.add(|_, name: String| Provider { name: name, id: 0 });
        c.add(|c, name: String| Chain {
            name: name.clone(),
            id: 0,
            default_provider: c.convert(name),
        });
        c.add(|c, b: AbstractBlock| Block {
            chain: c.convert(b.chain),
            height: b.height,
            id: 0,
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

        assert_eq!(block, expected);
    }
}
