use std::collections::BTreeMap;
use std::any::{Any, TypeId};

pub struct Converter {
    converts: BTreeMap<(TypeId, TypeId), Box<dyn Any>>,
}

impl Converter {
    pub fn new() -> Self {
        Self {
            converts: BTreeMap::new(),
        }
    }

    pub fn add<From:  Sized + Any, To: Sized + Any>(&mut self, f: fn(&Self, From) -> To) 
    {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        if !self.converts.contains_key(&type_ids) {
            self.converts.insert(type_ids, Box::new(f));
        }
    }

    pub fn convert<From: Sized + Any, To: Sized + Any>(&self, x: From) -> To
    {
        match self.get::<From, To>() {
            Some(f) => f(x),
            None => unreachable!(),
        }
    }    

    pub fn get<From: Sized + Any, To: Sized + Any>(&self) -> Option<Box<dyn Fn(From) -> To + '_>>
    {
        let type_ids = (TypeId::of::<From>(), TypeId::of::<To>());
        self.converts.get(&type_ids).and_then(|f| 
            f.downcast_ref::<fn(&Self, From) -> To>().and_then(|f|
                Some(Box::new(move |x: From| f(&self, x)) as Box<dyn Fn(From) -> To>)
            )
        )
    }    
}
