use std::{any::Any, panic::UnwindSafe};
use serde::de::DeserializeOwned;
use std::iter::Iterator;
use crate::tester::*;

#[allow(unused_variables)]
pub trait StateHandler<State> {
    fn init(&mut self, state: State) {}
    fn check(&mut self, state: State) {}
}
pub trait ActionHandler<Action> {
    fn handle(&mut self, action: Action);
}

pub enum Event {
    Init(Box<dyn Any>),
    Check(Box<dyn Any>),
    Action(Box<dyn Any>),
}

pub struct EventStream {
    events: Vec<Event>,
}

impl EventStream {
    pub fn new() -> EventStream {
        EventStream {
            events: vec![],
        }
    }

    pub fn init<T>(mut self, state: T) -> Self 
    where T: 'static
    {
        self.events.push(Event::Init(Box::new(state)));
        self
    }
 
    pub fn check<T>(mut self, state: T) -> Self 
    where T: 'static
    {
        self.events.push(Event::Check(Box::new(state)));
        self
    }

    pub fn action<T>(mut self, event: T) -> Self 
    where T: 'static
    {
        self.events.push(Event::Action(Box::new(event)));
        self
    }

}

impl IntoIterator for EventStream {
    type Item = Event;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.events.into_iter()
    }
}


pub struct Runner<'a, System> {
    pub inits: SystemTester<'a, System>,
    pub nexts: SystemTester<'a, System>,
    pub actions: SystemTester<'a, System>,
}

impl<'a, System> Runner<'a, System> {
    pub fn new() -> Self {
        Runner {
            inits: SystemTester::new(),
            nexts: SystemTester::new(),
            actions: SystemTester::new()
        }
    }

    pub fn with_state<S>(mut self) -> Self
    where 
        S: 'static + DeserializeOwned + UnwindSafe + Clone,
        System: 'static + StateHandler<S>
    {
        self.inits.add(StateHandler::<S>::init);
        self.nexts.add(StateHandler::<S>::check);
        self

    }

    pub fn with_action<A>(mut self) -> Self
    where 
        A: 'static + DeserializeOwned + UnwindSafe + Clone,
        System: 'static + ActionHandler<A>
    {
        self.actions.add(ActionHandler::<A>::handle);
        self
    }    
 
    pub fn run(&mut self, system: &mut System, stream: &mut dyn Iterator<Item = Event>) -> TestResult {
        while let Some(event) = stream.next() {
            let result = match event {
                Event::Init(input) => self.inits.test(system, &input),
                Event::Check(input)  => self.nexts.test(system, &input),
                Event::Action(input) => self.actions.test(system, &input)
            };
            match result {
                TestResult::Success => continue,
                other => return other,
            }
        }
        TestResult::Success
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Deserialize, Clone)]
    pub struct State1 {
        pub value: String,
    }

    #[derive(Deserialize, Clone)]
    pub struct State2 {
        pub value: String,
    }

    #[derive(Deserialize, Clone)]
    pub struct Action1 {
        pub value: String,
    }

    #[derive(Deserialize, Clone)]
    pub struct Action2 {
        pub value: String,
    }

    pub struct MySystem {
        pub state1: String,
        pub state2: String
    }

    impl StateHandler<State1> for MySystem {
        fn init(&mut self, state: State1) {
            self.state1 = state.value;
        }

        fn check(&mut self, state: State1) {
            assert!(self.state1 == state.value);
        }
    }

    impl StateHandler<State2> for MySystem {
        fn init(&mut self, state: State2) {
            self.state2 = state.value;
        }

        fn check(&mut self, state: State2) {
            assert!(self.state2 == state.value);
        }
    }

    impl ActionHandler<Action1> for MySystem {
        fn handle(&mut self, action: Action1) {
            self.state1 = action.value;
        }
    }

    impl ActionHandler<Action2> for MySystem {
        fn handle(&mut self, action: Action2) {
            self.state2 = action.value;
        }
    }


    #[test]
    fn test() {
        let events = EventStream::new()
            .init(State1{ value: "init state 1".to_string() })
            .init(State2{ value: "init state 2".to_string() })
            .init(State2{ value: "init state 2".to_string() })
            .action(Action1{ value: "action1 state".to_string() })
            .action(Action2{ value: "action2 state".to_string() })
            .check(State1{ value: "action1 state".to_string() })
            .check(State2{ value: "action2 state".to_string() });

        let mut runner = Runner::new()
            .with_state::<State1>()
            .with_state::<State2>()
            .with_action::<Action1>()
            .with_action::<Action2>();


        let mut system = MySystem { state1: "".to_string(), state2: "".to_string() };
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Success);
    }
}
