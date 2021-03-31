use crate::artifact::JsonTrace;
use crate::tester::*;
use serde::{de::DeserializeOwned, Serialize};
use serde_json::Value as JsonValue;
use std::iter::Iterator;
use std::{any::Any, fmt::Debug, panic::UnwindSafe};

/// A trait for handling the mapping between abstract and concrete system states
/// It is supposed that the tests are described in terms of a
/// (much simpler) abstract state,
/// with a lot less components than the concrete system state being tested.
///
/// A concrete system state can be partitioned into several state subspaces,
/// With separate abstract state describing each concrete state subspace.
#[allow(unused_variables)]
pub trait StateHandler<State> {
    /// Initialize concrete state from the abstract one.
    /// Should completely reinitialize the concrete state when called.
    /// Guaranteed to be called at the beginning of each test.
    fn init(&mut self, state: State);

    /// Read the concrete state into the abstract one.
    fn read(&self) -> State;
}

/// A trait for handling abstract test actions (messages).
pub trait ActionHandler<Action> {
    /// Type of action outcome. Set to () if none.
    type Outcome;

    /// Initialize processing of actions of that type.
    /// Guaranteed to be called at the beginning of each test
    fn init(&mut self) {}

    /// Process an action of that type & modify the concrete state as appropriate.
    /// The test produces the outcome, which may be checked later.
    fn handle(&mut self, action: Action) -> Self::Outcome;
}

/// A set of events to describe tests based on abstract states and actions.
#[derive(Debug)]
pub enum Event {
    /// Initialize the concrete system state from the abstract one.
    Init(Box<dyn Any>),
    /// Process the abstract action, modifying the system state.
    Action(Box<dyn Any>),
    /// Expect the provided outcome of the last action.
    Outcome(String),
    /// Check the assertion about the abstract system state.
    Check(Box<dyn Any>),
    /// Expect exactly the provided abstract system state.
    Expect(Box<dyn Any>),
}

/// A stream of events; defines the test.
#[derive(Debug)]
pub struct EventStream {
    events: Vec<Event>,
}

impl Default for EventStream {
    fn default() -> Self {
        EventStream::new()
    }
}

impl EventStream {
    /// Create a new event stream.
    pub fn new() -> EventStream {
        EventStream { events: vec![] }
    }

    /// Add an initial abstract state to the event stream.
    /// [StateHandler::init] should handle this event and
    /// initialize the concrete system state from it.
    /// Modifies the caller.
    pub fn add_init<T>(&mut self, state: T)
    where
        T: 'static,
    {
        self.events.push(Event::Init(Box::new(state)));
    }

    /// Add an initial abstract state to the event stream.
    /// [StateHandler::init] should handle this event and
    /// initialize the concrete system state from it.
    /// Produces the modified version of the caller,
    /// allowing to chain the events.
    pub fn init<T>(mut self, state: T) -> Self
    where
        T: 'static,
    {
        self.add_init(state);
        self
    }

    /// Add an abstract action to the event stream.
    /// [ActionHandler::handle] should handle the action and
    /// modify the concrete system state accordingly.
    /// Modifies the caller.
    pub fn add_action<T>(&mut self, action: T)
    where
        T: 'static,
    {
        self.events.push(Event::Action(Box::new(action)));
    }

    /// Add an abstract action to the event stream.
    /// [ActionHandler::handle] should handle the action and
    /// modify the concrete system state accordingly.
    /// Produces the modified version of the caller,
    /// allowing to chain the events.
    pub fn action<T>(mut self, action: T) -> Self
    where
        T: 'static,
    {
        self.add_action(action);
        self
    }

    /// Add the check for the previous action outcome to the event stream.
    /// [ActionHandler::handle] to which the previous actions was dispatched,
    /// should produce exactly this outcome.
    /// Modifies the caller.
    pub fn add_outcome<T>(&mut self, outcome: T)
    where
        T: 'static + Serialize,
    {
        self.events.push(Event::Outcome(
            serde_json::to_string_pretty(&outcome).unwrap(),
        ));
    }

    /// Add the check for the previous action outcome to the event stream.
    /// [ActionHandler::handle] to which the previous actions was dispatched,
    /// should produce exactly this outcome.
    /// Produces the modified version of the caller,
    /// allowing to chain the events.
    pub fn outcome<T>(mut self, outcome: T) -> Self
    where
        T: 'static + Serialize,
    {
        self.add_outcome(outcome);
        self
    }

    /// Add the assertion about the abstract system state to the event stream.
    /// The check is executed against the state returned by [StateHandler::read].
    /// Modifies the caller.
    pub fn add_check<T>(&mut self, assertion: fn(T))
    where
        T: 'static,
    {
        self.events.push(Event::Check(Box::new(assertion)));
    }

    /// Add the assertion about the abstract system state to the event stream.
    /// The check is executed against the state returned by [StateHandler::read].
    /// Produces the modified version of the caller,
    /// allowing to chain the events.
    pub fn check<T>(mut self, assertion: fn(T)) -> Self
    where
        T: 'static,
    {
        self.add_check(assertion);
        self
    }

    /// Add the expectation about the abstract system state to the event stream.
    /// The abstract state returned by [StateHandler::read] should exactly match.
    /// Modifies the caller.
    pub fn add_expect<T>(&mut self, state: T)
    where
        T: 'static,
    {
        self.events.push(Event::Expect(Box::new(state)));
    }

    /// Add the expectation about the abstract system state to the event stream.
    /// The abstract state returned by [StateHandler::read] should exactly match.
    /// Modifies the caller.
    /// Produces the modified version of the caller,
    /// allowing to chain the events.
    pub fn expect<T>(mut self, state: T) -> Self
    where
        T: 'static,
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

impl From<JsonTrace> for EventStream {
    fn from(trace: JsonTrace) -> Self {
        let mut events = EventStream::new();
        for (index, value) in trace.into_iter().enumerate() {
            if index == 0 {
                events.add_init(value);
            } else {
                if let JsonValue::Object(value) = value.clone() {
                    if let Some(action) = value.get("action") {
                        events.add_action(action.clone());
                    };
                    if let Some(outcome) = value.get("actionOutcome") {
                        events.add_outcome(outcome.clone());
                    }
                }
                events.add_expect(value);
            }
        }
        events
    }
}

/// A runner that allows to run tests specified as event streams
/// against the given concrete system.
/// You can implement several instances of [StateHandler]s
/// and [ActionHandler]s for the `System`, thus allowing your system
/// to handle several kinds of abstract states or actions.
pub struct Runner<'a, System> {
    inits: SystemTester<'a, System>,
    actions: SystemTester<'a, System>,
    checks: SystemTester<'a, System>,
    expects: SystemTester<'a, System>,
    outcome: String,
}

impl<'a, System> Default for Runner<'a, System> {
    fn default() -> Self {
        Runner::new()
    }
}

impl<'a, System> Runner<'a, System> {
    /// Create a new runner for the given `System`.
    pub fn new() -> Self {
        Runner {
            inits: SystemTester::new(),
            actions: SystemTester::new(),
            checks: SystemTester::new(),
            expects: SystemTester::new(),
            outcome: String::new(),
        }
    }

    /// Equip the runner with the ability to handle given abstract `State`.
    pub fn with_state<State>(mut self) -> Self
    where
        State: 'static + DeserializeOwned + UnwindSafe + Clone + Debug + PartialEq,
        System: 'static + StateHandler<State>,
    {
        self.inits.add(StateHandler::<State>::init);
        self.checks
            .add_fn(|system, assertion: fn(State)| assertion(system.read()));
        self.expects
            .add(|system, state: State| assert_eq!(system.read(), state));
        self
    }

    /// Equip the runner with the ability to handle given abstract `Action`.
    pub fn with_action<Action>(mut self) -> Self
    where
        Action: 'static + DeserializeOwned + UnwindSafe + Clone,
        System: 'static + ActionHandler<Action>,
        <System as ActionHandler<Action>>::Outcome: 'static + Serialize,
    {
        self.actions.add(ActionHandler::<Action>::handle);
        self
    }

    /// Run the runner on:
    /// - the given concrete `system`,
    ///   which provides storage of concrete system states,
    ///   as well as the handling of the abstract states and actions;
    /// - the given stream of events, representing the test.
    ///
    /// Returns the test result.
    pub fn run(
        &mut self,
        system: &mut System,
        stream: &mut dyn Iterator<Item = Event>,
    ) -> TestResult {
        for event in stream {
            let result = match event {
                Event::Init(input) => self.inits.test(system, &input),
                Event::Action(input) => self.actions.test(system, &input),
                Event::Outcome(expected) => {
                    if self.outcome == expected {
                        TestResult::Success(self.outcome.clone())
                    } else {
                        TestResult::Failure {
                            message: format!(
                                "Expected action outcome '{}', got '{}'",
                                expected, self.outcome
                            ),
                            location: String::new(),
                        }
                    }
                }
                Event::Check(assertion) => self.checks.test(system, &assertion),
                Event::Expect(assertion) => self.expects.test(system, &assertion),
            };
            match result {
                TestResult::Success(res) => self.outcome = res,
                other => return other,
            }
        }
        TestResult::Success(String::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::artifact::JsonTrace;
    use serde::{Deserialize, Serialize};
    use serde_json::Value;

    #[derive(Deserialize, Serialize, Clone, Debug, PartialEq)]
    struct State1 {
        state1: String,
    }

    #[derive(Deserialize, Serialize, Clone, Debug, PartialEq)]
    struct State2 {
        state2: String,
    }

    #[derive(Deserialize, Serialize, Clone)]
    struct Action1 {
        value1: String,
    }

    #[derive(Serialize)]
    enum Outcome {
        Success(String),
        Failure(String),
    }

    #[derive(Deserialize, Serialize, Clone)]
    struct Action2 {
        value2: String,
    }

    struct MySystem {
        state1: String,
        state2: String,
    }

    impl StateHandler<State1> for MySystem {
        fn init(&mut self, state: State1) {
            self.state1 = state.state1;
        }

        fn read(&self) -> State1 {
            State1 {
                state1: self.state1.clone(),
            }
        }
    }

    impl StateHandler<State2> for MySystem {
        fn init(&mut self, state: State2) {
            self.state2 = state.state2;
        }

        fn read(&self) -> State2 {
            State2 {
                state2: self.state2.clone(),
            }
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
            .init(State1 {
                state1: "init state 1".to_string(),
            })
            .init(State2 {
                state2: "init state 2".to_string(),
            })
            .action(Action1 {
                value1: "action1 state".to_string(),
            })
            .outcome(Outcome::Success("OK".to_string()))
            .action(Action2 {
                value2: "action2 state".to_string(),
            })
            .outcome(Outcome::Failure("NOT OK".to_string()))
            .check(|state: State1| assert!(state.state1 == "action1 state"))
            .expect(State2 {
                state2: "action2 state".to_string(),
            });

        let mut runner = Runner::new()
            .with_state::<State1>()
            .with_state::<State2>()
            .with_action::<Action1>()
            .with_action::<Action2>();

        let mut system = MySystem {
            state1: "".to_string(),
            state2: "".to_string(),
        };
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

        let mut system = MySystem {
            state1: "".to_string(),
            state2: "".to_string(),
        };

        // Unknown action with value3 field
        let trace: JsonTrace = vec![
            r#"{ "state1": "init state 1", "state2": "init state 2" }"#,
            r#"{ "action": { "value3": "action1 state" },
                 "state1": "action1 state", "state2": "init state 2" }"#,
        ]
        .into_iter()
        .map(|x| serde_json::from_str(x).unwrap())
        .collect::<Vec<Value>>()
        .into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert_eq!(result, TestResult::Unhandled);

        let trace: JsonTrace = vec![
            r#"{ "state1": "init state 1", "state2": "init state 2" }"#,
            r#"{ "action": { "value1": "action1 state" },
                 "actionOutcome": { "Success": "OK" },
                 "state1": "action1 state", "state2": "init state 2" }"#,
            r#"{ "action": { "value2": "action2 state" },
                 "actionOutcome": { "Failure": "NOT OK" },
                 "state1": "action1 state", "state2": "action2 state" }"#,
        ]
        .into_iter()
        .map(|x| serde_json::from_str(x).unwrap())
        .collect::<Vec<Value>>()
        .into();

        let events: EventStream = trace.into();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert!(matches!(result, TestResult::Success(_)));
    }
}
