use std::{any::Any, panic::UnwindSafe, fmt::Debug};
use serde::{Serialize, de::DeserializeOwned};
use std::iter::Iterator;
use crate::tester::*;

#[allow(unused_variables)]
pub trait StateHandler<State> {
    // Initialize concrete state from the abstract one.
    // Should completely reinitialize the concrete state when called.
    // Guaranteed to be called at the beginning of each test.
    fn init(&mut self, state: State);

    // Read the concrete state into the abstract one.
    fn read(&self) -> State;


}
pub trait ActionHandler<Action> {
    // Type of action outcome. Set to () if none.
    type Outcome;

    // Initialize processing of actions of that type.
    // Guaranteed to be called at the beginning of each test
    fn init(&mut self) {}

    // Process an action of that type & modify the concrete state as appropriate.
    // The produces the outcome, which can be checked later.
    fn handle(&mut self, action: Action) -> Self::Outcome;
}

pub enum Event {
    Init(Box<dyn Any>),
    Action(Box<dyn Any>),
    Outcome(String),
    Check(Box<dyn Any>),
    Expect(Box<dyn Any>),
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

    pub fn add_outcome<T>(&mut self, outcome: T) 
    where   T: 'static + Serialize,
    {
        self.events.push(Event::Outcome(serde_json::to_string_pretty(&outcome).unwrap()));
    }

    pub fn outcome<T>(mut self, outcome: T) -> Self 
    where T: 'static + Serialize,
    {
        self.add_outcome(outcome);
        self
    }

    pub fn add_check<T>(&mut self, assertion: fn(T)) 
    where T: 'static

    {
        self.events.push(Event::Check(Box::new(assertion as fn(T))));
    }    

    pub fn check<T>(mut self, assertion: fn(T)) -> Self 
    where T: 'static
    {
        self.add_check(assertion);
        self
    }

    pub fn add_expect<T>(&mut self, state: T) 
    where T: 'static
    {
        self.events.push(Event::Expect(Box::new(state)));
    }

    pub fn expect<T>(mut self, state: T) -> Self 
    where T: 'static
    {
        self.add_expect(state);
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
    pub actions: SystemTester<'a, System>,
    pub checks: SystemTester<'a, System>,
    pub expects: SystemTester<'a, System>,
    pub outcome: String,
}

impl<'a, System> Runner<'a, System> {
    pub fn new() -> Self {
        Runner {
            inits: SystemTester::new(),
            actions: SystemTester::new(),
            checks: SystemTester::new(),
            expects: SystemTester::new(),
            outcome: String::new(),
        }
    }

    pub fn with_state<S>(mut self) -> Self
    where 
        S: 'static + DeserializeOwned + UnwindSafe + Clone + Debug + PartialEq,
        System: 'static + StateHandler<S>
    {
        self.inits.add(StateHandler::<S>::init);
        self.checks.add_fn(|system, assertion: fn(S)| assertion(system.read()));
        self.expects.add(|system, state: S| assert_eq!(system.read(), state));
        self

    }

    pub fn with_action<A>(mut self) -> Self
    where 
        A: 'static + DeserializeOwned + UnwindSafe + Clone,
        System: 'static + ActionHandler<A>,
        <System as ActionHandler<A>>::Outcome: 'static + Serialize 
    {
        self.actions.add( ActionHandler::<A>::handle);
        self
    }    
 
    pub fn run(&mut self, system: &mut System, stream: &mut dyn Iterator<Item = Event>) -> TestResult {
        while let Some(event) = stream.next() {
            let result = match event {
                Event::Init(input) => self.inits.test(system, &input),
                Event::Action(input) => self.actions.test(system, &input),
                Event::Outcome(expected) => 
                    if self.outcome == expected {
                        TestResult::Success(self.outcome.clone())
                    }
                    else {
                        TestResult::Failure {
                            message: format!("Expected action outcome '{}', got '{}'", expected, self.outcome),
                            location: String::new(),
                        }
                    },
                Event::Check(assertion) => self.checks.test(system, &assertion),
                Event::Expect(assertion) => self.expects.test(system, &assertion)
            };
            match result {
                TestResult::Success(res) =>  self.outcome = res,
                other => return other,
            }
        }
        TestResult::Success(String::new())
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};
    use serde_json::Value;
    use crate::artifact::JsonTrace;

    #[derive(Deserialize, Serialize, Clone, Debug, PartialEq)]
    pub struct State1 {
        pub state1: String,
    }

    #[derive(Deserialize, Serialize, Clone, Debug, PartialEq)]
    pub struct State2 {
        pub state2: String,
    }

    #[derive(Deserialize, Serialize, Clone)]
    pub struct Action1 {
        pub value1: String,
    }

    #[derive(Serialize)]
    pub enum Outcome {
        Success(String),
        Failure(String)
    }

    #[derive(Deserialize, Serialize, Clone)]
    pub struct Action2 {
        pub value2: String,
    }

    pub struct MySystem {
        pub state1: String,
        pub state2: String,
    }

    impl StateHandler<State1> for MySystem {
        fn init(&mut self, state: State1) {
            self.state1 = state.state1;
        }

        fn read(&self) -> State1 {
            State1 { state1: self.state1.clone() }
        }
    }

    impl StateHandler<State2> for MySystem {
        fn init(&mut self, state: State2) {
            self.state2 = state.state2;
        }

        fn read(&self) -> State2 {
            State2 { state2: self.state2.clone() }
        }
    }

    impl ActionHandler<Action1> for MySystem {
        type Outcome = Outcome;

        fn handle(&mut self, action: Action1) -> Outcome {
            self.state1 = action.value1;
            Outcome::Success("OK".to_string())
        }
    }

    impl ActionHandler<Action2> for MySystem {
        type Outcome = Outcome;

        fn handle(&mut self, action: Action2) -> Outcome {
            self.state2 = action.value2;
            Outcome::Failure("NOT OK".to_string())
        }
    }


    #[test]
    fn test_stream() {
        let events = EventStream::new()
            .init(State1{ state1: "init state 1".to_string() })
            .init(State2{ state2: "init state 2".to_string() })
            .action(Action1{ value1: "action1 state".to_string()})
            .outcome(Outcome::Success("OK".to_string()))
            .action(Action2{ value2: "action2 state".to_string()})
            .outcome(Outcome::Failure("NOT OK".to_string()))
            .check(|state: State1| assert!(state.state1 == "action1 state"))
            .expect( State2 { state2: "action2 state".to_string()})
            ;

        let mut runner = Runner::new()
            .with_state::<State1>()
            .with_state::<State2>()
            .with_action::<Action1>()
            .with_action::<Action2>()
            ;


        let mut system = MySystem { state1: "".to_string(), state2: "".to_string() };
        let result = runner.run(&mut system, &mut events.into_iter());
        assert!(matches!(result, TestResult::Success(_)));
    }

    #[test]
    fn test_json_trace() {
        let mut runner = Runner::new()
            .with_state::<State1>()
            .with_state::<State2>()
            .with_action::<Action1>()
            .with_action::<Action2>();

        let mut system = MySystem { state1: "".to_string(), state2: "".to_string() };

        // Unknown action with value3 field
        let trace: JsonTrace = vec! [
            r#"{ "state1": "init state 1", "state2": "init state 2" }"#,
            r#"{ "action": { "value3": "action1 state" },
                 "state1": "action1 state", "state2": "init state 2" }"#,
        ].into_iter().map(|x| serde_json::from_str(x).unwrap()).collect::<Vec<Value>>().into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Unhandled);


        let trace: JsonTrace = vec! [
            r#"{ "state1": "init state 1", "state2": "init state 2" }"#,
            r#"{ "action": { "value1": "action1 state" },
                 "actionOutcome": { "Success": "OK" },
                 "state1": "action1 state", "state2": "init state 2" }"#,
            r#"{ "action": { "value2": "action2 state" },
                 "actionOutcome": { "Failure": "NOT OK" },
                 "state1": "action1 state", "state2": "action2 state" }"#
        ].into_iter().map(|x| serde_json::from_str(x).unwrap()).collect::<Vec<Value>>().into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert!(matches!(result, TestResult::Success(_)));
    }    
}
