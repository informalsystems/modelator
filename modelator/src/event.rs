use std::{any::Any, panic::UnwindSafe};
use serde::de::DeserializeOwned;
use std::iter::Iterator;
use crate::tester::*;

pub trait StateSystem<State> {
    fn init(&mut self, state: State);
    fn next(&mut self, state: State);
}
pub trait ActionHandler<Action> {
    fn handle(&mut self, action: Action);
}

pub enum Event {
    Init(Box<dyn Any>),
    Next(Box<dyn Any>),
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

    pub fn init<T>(mut self, event: T) -> Self 
    where T: 'static
    {
        self.events.push(Event::Init(Box::new(event)));
        self
    }
 
    pub fn next<T>(mut self, event: T) -> Self 
    where T: 'static
    {
        self.events.push(Event::Next(Box::new(event)));
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
    inits: SystemTester<'a, System>,
    nexts: SystemTester<'a, System>,
    actions: SystemTester<'a, System>,
}

impl<'a, System> Runner<'a, System> {
    pub fn new() -> Self {
        Runner {
            inits: SystemTester::new(),
            nexts: SystemTester::new(),
            actions: SystemTester::new()
        }
    }

    pub fn with_state_system<S>(mut self) -> Self
    where 
        S: 'static + DeserializeOwned + UnwindSafe + Clone,
        System: 'static + StateSystem<S>
    {
        self.inits.add(StateSystem::<S>::init);
        self.nexts.add(StateSystem::<S>::next);
        self

    }

    pub fn with_action_handler<A>(mut self) -> Self
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
                Event::Next(input)  => self.nexts.test(system, &input),
                Event::Action(input) => self.actions.test(system, &input)
            };
            match result {
                TestResult::Success => continue,
                other => return other
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
    pub struct State {
        pub name: String,
    }

    #[derive(Deserialize, Clone)]
    pub struct Action1 {
        pub name: String,
    }

    #[derive(Deserialize, Clone)]
    pub struct Action2 {
        pub name: String,
    }

    pub struct MySystem {
        pub state: String
    }

    impl StateSystem<State> for MySystem {
        fn init(&mut self, state: State) {
            self.state = state.name;
        }
        fn next(&mut self, state: State) {
            self.state = state.name;
        }
    }

    impl ActionHandler<Action1> for MySystem {
        fn handle(&mut self, action: Action1) {
            self.state = action.name;
        }
    }

    impl ActionHandler<Action2> for MySystem {
        fn handle(&mut self, action: Action2) {
            self.state = action.name;
        }
    }


    #[test]
    fn test() {
        let events = EventStream::new()
            .init(State{ name: "init".to_string() })
            .next(State{ name: "next".to_string() })
            .action(Action1{ name: "action1".to_string() })
            .action(Action2{ name: "action2".to_string() });

        let mut system = MySystem { state: "".to_string() };

        let mut runner = Runner::new()
            .with_state_system::<State>()
            .with_action_handler::<Action1>()
            .with_action_handler::<Action2>();


        let result = runner.run(&mut system, &mut events.into_iter());
        println!("{:?}", result);
    }
}
