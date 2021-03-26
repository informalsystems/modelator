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

    pub fn add_init<T>(&mut self, state: T) 
    where T: 'static
    {
        self.events.push(Event::Init(Box::new(state)));
    }
 
    pub fn init<T>(mut self, state: T) -> Self 
    where T: 'static
    {
        self.add_init(state);
        self
    }
 
    pub fn add_check<T>(&mut self, state: T) 
    where T: 'static
    {
        self.events.push(Event::Check(Box::new(state)));
    }

    pub fn check<T>(mut self, state: T) -> Self 
    where T: 'static
    {
        self.add_check(state);
        self
    }

    pub fn add_action<T>(&mut self, action: T) 
    where T: 'static
    {
        self.events.push(Event::Action(Box::new(action)));
    }

    pub fn action<T>(mut self, action: T) -> Self 
    where T: 'static
    {
        self.add_action(action);
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
                Event::Init(input) => self.inits.test_all(system, &input),
                Event::Check(input)  => self.nexts.test_all(system, &input),
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
    use serde::{Deserialize, Serialize};
    use serde_json::Value;
    use crate::artifact::JsonTrace;

    #[derive(Deserialize, Serialize, Clone)]
    pub struct State1 {
        pub state1: String,
    }

    #[derive(Deserialize, Serialize, Clone)]
    pub struct State2 {
        pub state2: String,
    }

    #[derive(Deserialize, Serialize, Clone)]
    pub struct Action1 {
        pub value1: String,
        pub outcome: String
    }

    #[derive(Deserialize, Serialize, Clone)]
    pub struct Action2 {
        pub value2: String,
        pub outcome: String
    }

    pub struct MySystem {
        pub state1: String,
        pub state2: String
    }

    impl StateHandler<State1> for MySystem {
        fn init(&mut self, state: State1) {
            self.state1 = state.state1;
        }

        fn check(&mut self, state: State1) {
            assert!(self.state1 == state.state1);
        }
    }

    impl StateHandler<State2> for MySystem {
        fn init(&mut self, state: State2) {
            self.state2 = state.state2;
        }

        fn check(&mut self, state: State2) {
            assert!(self.state2 == state.state2);
        }
    }

    impl ActionHandler<Action1> for MySystem {
        fn handle(&mut self, action: Action1) {
            self.state1 = action.value1;
            assert!(action.outcome == "OK");
        }
    }

    impl ActionHandler<Action2> for MySystem {
        fn handle(&mut self, action: Action2) {
            self.state2 = action.value2;
            assert!(action.outcome == "OK");
        }
    }


    #[test]
    fn test_stream() {
        let events = EventStream::new()
            .init(State1{ state1: "init state 1".to_string() })
            .init(State2{ state2: "init state 2".to_string() })
            .action(Action1{ value1: "action1 state".to_string(), outcome: "OK".to_string() })
            .action(Action2{ value2: "action2 state".to_string(), outcome: "OK".to_string() })
            .check(State1{ state1: "action1 state".to_string() })
            .check(State2{ state2: "action2 state".to_string() });

        let mut runner = Runner::new()
            .with_state::<State1>()
            .with_state::<State2>()
            .with_action::<Action1>()
            .with_action::<Action2>();


        let mut system = MySystem { state1: "".to_string(), state2: "".to_string() };
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Success);
    }

    #[test]
    fn test_json_trace() {
        let mut runner = Runner::new()
            .with_state::<State1>()
            .with_state::<State2>()
            .with_action::<Action1>()
            .with_action::<Action2>();

        let mut system = MySystem { state1: "".to_string(), state2: "".to_string() };

         // Not all state components specified initially
         let trace: JsonTrace = vec! [
            r#"{ "state1": "init state 1" }"#,
        ].into_iter().map(|x| serde_json::from_str(x).unwrap()).collect::<Vec<Value>>().into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Unhandled);


         // Not all state components specified in a check
         let trace: JsonTrace = vec! [
            r#"{ "state1": "init state 1", "state2": "init state 2" }"#,
            r#"{ "action": { "value3": "action1 state", "outcome": "OK" },
                 "state2": "init state 2" }"#,
        ].into_iter().map(|x| serde_json::from_str(x).unwrap()).collect::<Vec<Value>>().into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Unhandled);

        // Unknown action with value3 field
        let trace: JsonTrace = vec! [
            r#"{ "state1": "init state 1", "state2": "init state 2" }"#,
            r#"{ "action": { "value3": "action1 state", "outcome": "OK" },
                 "state1": "action1 state", "state2": "init state 2" }"#,
        ].into_iter().map(|x| serde_json::from_str(x).unwrap()).collect::<Vec<Value>>().into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Unhandled);


        let trace: JsonTrace = vec! [
            r#"{ "state1": "init state 1", "state2": "init state 2" }"#,
            r#"{ "action": { "value1": "action1 state", "outcome": "OK" },
                 "state1": "action1 state", "state2": "init state 2" }"#,
            r#"{ "action": { "value2": "action2 state", "outcome": "OK" },
                "state1": "action1 state", "state2": "action2 state" }"#
        ].into_iter().map(|x| serde_json::from_str(x).unwrap()).collect::<Vec<Value>>().into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Success);
    }    
}
