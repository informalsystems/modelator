use crate::util::*;
use serde::{de::DeserializeOwned, Serialize};
use serde_json::Value;
use std::{
    any::Any,
    panic::{self, AssertUnwindSafe, UnwindSafe},
    sync::{Arc, Mutex},
};

/// Result of executing a test or a set of tests.
#[derive(Debug, Clone, PartialEq)]
pub enum TestResult {
    /// Successful test execution, with serialized result.
    Success(String),
    /// Test(s) failed, with the given message and at the given location.
    Failure { message: String, location: String },
    /// Test input was unhandled: no test for it has been defined.
    Unhandled,
}

/// A simple test is a test that accepts a single input,
/// and produces a test result
type SimpleTest<'a> = Box<dyn FnMut(&dyn Any) -> TestResult + 'a>;

/// SimpleTester represents a collection of simple test functions,
/// where each function can handle a specific kind of input.
pub struct SimpleTester<'a> {
    tests: Vec<SimpleTest<'a>>,
}

impl<'a> Default for SimpleTester<'a> {
    fn default() -> Self {
        SimpleTester::new()
    }
}

impl<'a> SimpleTester<'a> {
    pub fn new() -> SimpleTester<'a> {
        SimpleTester { tests: vec![] }
    }

    /// Add a test function to the tester.
    pub fn add<T, F, R>(&mut self, mut test: F)
    where
        T: 'static + DeserializeOwned + UnwindSafe + Clone,
        F: FnMut(T) -> R + 'a,
        R: 'static + Serialize,
    {
        let test_fn = move |input: &dyn Any| match convert_to::<T>(input) {
            Some(test_case) => capture_test(|| test(test_case.clone())),
            None => TestResult::Unhandled,
        };
        self.tests.push(Box::new(test_fn));
    }

    /// Add to the tester a test function that can accept closures as input.
    pub fn add_fn<T, F, R>(&mut self, mut test: F)
    where
        T: 'static + UnwindSafe + Clone,
        F: FnMut(T) + 'a,
        R: 'static + Serialize,
    {
        let test_fn = move |input: &dyn Any| match interpret_as::<T>(input) {
            Some(test_case) => capture_test(|| test(test_case.clone())),
            None => TestResult::Unhandled,
        };
        self.tests.push(Box::new(test_fn));
    }

    /// Run the test functions on the provided input.
    /// The first test function that is able to handle this kind of input,
    /// will produce the result. If none of the defined test functions is
    /// able to handle the input, the `unhandled` result will be returned.
    pub fn test(&mut self, input: &dyn Any) -> TestResult {
        let mut last = TestResult::Unhandled;
        for test in &mut self.tests {
            let res = test(input);
            match (&last, res) {
                // On failure return immediately
                (_, res @ TestResult::Failure { .. }) => return res,
                // If previously unhandled -> update
                (TestResult::Unhandled, res) => last = res,
                // All other cases (Success, Unhandled), (Success, Success) -> do nothing
                _ => (),
            };
        }
        last
    }
}

/// A SystemTest is a test function that accepts some system,
/// which stores modifiable state, and the input.
type SystemTest<'a, State> = Box<dyn FnMut(&mut State, &dyn Any) -> TestResult + 'a>;

/// SystemTester is similar to [SimpleTester], but allows to
/// supply test functions that accept also modifiable system state.
pub struct SystemTester<'a, State> {
    tests: Vec<SystemTest<'a, State>>,
}

impl<'a, State> Default for SystemTester<'a, State> {
    fn default() -> Self {
        SystemTester::new()
    }
}

impl<'a, State> SystemTester<'a, State> {
    pub fn new() -> SystemTester<'a, State> {
        SystemTester { tests: vec![] }
    }

    /// Add a test function to the tester.
    pub fn add<T, F, R>(&mut self, mut test: F)
    where
        T: 'static + DeserializeOwned + UnwindSafe + Clone,
        F: FnMut(&mut State, T) -> R + 'a,
        R: 'static + Serialize,
    {
        let test_fn = move |state: &mut State, input: &dyn Any| match convert_to::<T>(input) {
            Some(test_case) => capture_test(|| test(state, test_case.clone())),
            None => TestResult::Unhandled,
        };
        self.tests.push(Box::new(test_fn));
    }

    /// Add to the tester a test function that can accept closures as input.
    pub fn add_fn<T, F, R>(&mut self, mut test: F)
    where
        T: 'static + UnwindSafe + Clone,
        F: FnMut(&mut State, T) -> R + 'a,
        R: 'static + Serialize,
    {
        let test_fn = move |state: &mut State, input: &dyn Any| match interpret_as::<T>(input) {
            Some(test_case) => capture_test(|| test(state, test_case.clone())),
            None => TestResult::Unhandled,
        };
        self.tests.push(Box::new(test_fn));
    }

    /// Run the test functions on the provided system and input.
    /// The first test function that is able to handle this kind of input,
    /// will produce the result. If none of the defined test functions is
    /// able to handle the input, the `unhandled` result will be returned.
    pub fn test(&mut self, state: &mut State, input: &dyn Any) -> TestResult {
        let mut last = TestResult::Unhandled;
        for test in &mut self.tests {
            let res = test(state, input);
            match (&last, res) {
                // On failure return immediately
                (_, res @ TestResult::Failure { .. }) => return res,
                // If previously unhandled -> update
                (TestResult::Unhandled, res) => last = res,
                // All other cases (Success, Unhandled), (Success, Success) -> do nothing
                _ => (),
            };
        }
        last
    }
}

fn capture_test<'a, F, R>(mut test: F) -> TestResult
where
    F: FnMut() -> R + 'a,
    R: Serialize,
{
    let test_result = Arc::new(Mutex::new(TestResult::Unhandled));
    let old_hook = panic::take_hook();
    panic::set_hook({
        let result = test_result.clone();
        Box::new(move |info| {
            let mut result = result.lock().unwrap();
            let message = match info.payload().downcast_ref::<&'static str>() {
                Some(s) => s.to_string(),
                None => match info.payload().downcast_ref::<String>() {
                    Some(s) => s.clone(),
                    None => "Unknown error".to_string(),
                },
            };
            let location = match info.location() {
                Some(l) => l.to_string(),
                None => "".to_string(),
            };
            *result = TestResult::Failure { message, location };
        })
    });
    let result = panic::catch_unwind(AssertUnwindSafe(|| test()));
    panic::set_hook(old_hook);
    match result {
        Ok(res) => TestResult::Success(serde_json::to_string_pretty(&res).unwrap()),
        Err(_) => (*test_result.lock().unwrap()).clone(),
    }
}

fn convert_to<T>(input: &dyn Any) -> Option<T>
where
    T: 'static + DeserializeOwned + Clone,
{
    if let Some(test_case) = input.downcast_ref::<T>() {
        Some(test_case.clone())
    } else if let Some(input) = input.downcast_ref::<String>() {
        parse_from_str::<T>(input).ok()
    } else if let Some(input) = input.downcast_ref::<Value>() {
        parse_from_value::<T>(input.clone()).ok()
    } else if let Some(input) = input.downcast_ref::<Box<T>>() {
        Some((**input).clone())
    } else if let Some(input) = input.downcast_ref::<Box<String>>() {
        parse_from_str::<T>(&**input).ok()
    } else if let Some(input) = input.downcast_ref::<Box<Value>>() {
        parse_from_value::<T>((**input).clone()).ok()
    } else if let Some(input) = input.downcast_ref::<Box<dyn Any>>() {
        convert_to::<T>(&**input)
    } else {
        None
    }
}

fn interpret_as<T>(input: &dyn Any) -> Option<T>
where
    T: 'static + Clone,
{
    if let Some(test_case) = input.downcast_ref::<T>() {
        Some(test_case.clone())
    } else if let Some(input) = input.downcast_ref::<Box<T>>() {
        Some((**input).clone())
    } else if let Some(input) = input.downcast_ref::<Box<dyn Any>>() {
        interpret_as::<T>(&**input)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Deserialize, Clone)]
    pub struct MyTest {
        pub name: String,
    }

    #[derive(Deserialize, Clone)]
    pub struct MyTest2 {
        pub id: u64,
    }

    fn fails(_: MyTest2) {
        assert!(false);
    }

    fn succeeds_if_my_test(t: MyTest) {
        assert!(t.name == "my_test", "got {}", t.name);
    }

    pub struct MyState {
        pub state: String,
    }

    impl MyState {
        pub fn test1(&mut self, _: MyTest) {}

        pub fn test2(&mut self, _: MyTest2) {}
    }

    #[test]
    fn test() {
        let mut tester = SimpleTester::new();
        tester.add(fails);
        tester.add(succeeds_if_my_test);

        let res = tester.test(&"".to_string());
        assert!(res == TestResult::Unhandled);

        let data = String::from("{\"name\": \"test\"}");
        let res = tester.test(&data);
        assert!(
            matches!(res, TestResult::Failure { message, location: _ } if message == "got test")
        );

        let data = MyTest {
            name: "my_test".to_string(),
        };
        let res = tester.test(&data);
        assert!(matches!(res, TestResult::Success(_)));

        let data = String::from("{\"name\": \"my_test\"}");
        let res = tester.test(&data);
        println!("{:?}", res);
        assert!(matches!(res, TestResult::Success(_)));

        let data: Value = serde_json::from_str(&data).unwrap();
        let res = tester.test(&data);
        assert!(matches!(res, TestResult::Success(_)));

        let mut tester = SystemTester::<MyState>::new();
        tester.add(MyState::test1);
        tester.add(MyState::test2);
    }
}
