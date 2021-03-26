use crate::util::*;
use serde::de::DeserializeOwned;
use serde_json::Value;
use std::{
    any::Any,
    panic::{self, AssertUnwindSafe, UnwindSafe},
    sync::{Arc, Mutex},
};

#[derive(Debug, Clone, PartialEq)]
pub enum TestResult {
    Success,
    Failure { message: String, location: String },
    Unhandled,
}


type SimpleTest<'a> = Box<dyn FnMut(&dyn Any) -> TestResult + 'a>;

pub struct SimpleTester<'a> {
    tests: Vec<SimpleTest<'a>>,
}

impl<'a> SimpleTester<'a> {
    pub fn new() -> SimpleTester<'a> {
        SimpleTester { tests: vec![] }
    }

    pub fn add<T, F>(&mut self, mut test: F)
    where
        T: 'static + DeserializeOwned + UnwindSafe + Clone,
        F: FnMut(T) + 'a,
    {
        let test_fn = move |input: &dyn Any| {
            match convert_to::<T>(input) {
                Some(test_case) => capture_test(|| test(test_case.clone())),
                None => TestResult::Unhandled
            }
        };
        self.tests.push(Box::new(test_fn));
    }

    pub fn test(&mut self, input: &dyn Any) -> TestResult {
        for test in &mut self.tests {
            match test(input) {
                TestResult::Unhandled => continue,
                res => return res,
            }
        }
        TestResult::Unhandled
    }
}

type SystemTest<'a, State> = Box<dyn FnMut(&mut State, &dyn Any) -> TestResult + 'a>;


pub struct SystemTester<'a, State> {
    tests: Vec<SystemTest<'a, State>>,
}

impl<'a, State> SystemTester<'a, State> {
    pub fn new() -> SystemTester<'a, State> {
        SystemTester { tests: vec![] }
    }

    pub fn add<T, F>(&mut self, mut test: F)
    where
        T: 'static + DeserializeOwned + UnwindSafe + Clone,
        F: FnMut(&mut State, T) + 'a,
    {
        let test_fn = move |state: &mut State, input: &dyn Any| {
            match convert_to::<T>(input) {
                Some(test_case) => capture_test(|| test(state, test_case.clone())),
                None => TestResult::Unhandled
            }
        };
        self.tests.push(Box::new(test_fn));
    }

    pub fn test(&mut self, state: &mut State, input: &dyn Any) -> TestResult {
        for test in &mut self.tests {
            match test(state, input) {
                TestResult::Unhandled => continue,
                res => return res,
            }
        }
        TestResult::Unhandled
    }
}

fn capture_test<'a, F>(mut test: F) -> TestResult
where
    F: FnMut() + 'a,
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
        Ok(_) => TestResult::Success,
        Err(_) => (*test_result.lock().unwrap()).clone(),
    }
}

fn convert_to<T>(input: &dyn Any) -> Option<T>
where T: 'static + DeserializeOwned + Clone
{
    if let Some(test_case) = input.downcast_ref::<T>() {
        Some(test_case.clone())
    }
    else if let Some(input) = input.downcast_ref::<String>() {
        parse_from_str::<T>(input).ok()
    }
    else if let Some(input) = input.downcast_ref::<Value>() {
        parse_from_value::<T>(input.clone()).ok()
    }
    else if let Some(input) = input.downcast_ref::<Box<T>>() {
        Some((**input).clone())
    }
    else if let Some(input) = input.downcast_ref::<Box<String>>() {
        parse_from_str::<T>(&**input).ok()
    }
    else if let Some(input) = input.downcast_ref::<Box<Value>>() {
        parse_from_value::<T>((**input).clone()).ok()
    }
    else if let Some(input) = input.downcast_ref::<Box<dyn Any>>() {
        convert_to::<T>(&**input)
    } 
    else {
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
        pub state: String
    }

    impl MyState {
        pub fn test1(&mut self, _: MyTest) {

        }

        pub fn test2(&mut self, _: MyTest2) {
            
        }

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
        assert!(res == TestResult::Success);

        let data = String::from("{\"name\": \"my_test\"}");
        let res = tester.test(&data);
        println!("{:?}", res);
        assert!(res == TestResult::Success);

        let data: Value = serde_json::from_str(&data).unwrap();
        let res = tester.test(&data);
        assert!(res == TestResult::Success);

        let mut tester = SystemTester::<MyState>::new();
        tester.add(MyState::test1);
        tester.add(MyState::test2);

    }
}

