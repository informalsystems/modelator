use crate::util::*;
use serde::de::DeserializeOwned;
use std::{
    panic::{self, RefUnwindSafe, UnwindSafe},
    sync::{Arc, Mutex},
};

#[derive(Debug, Clone, PartialEq)]
pub enum TestResult {
    ParseError(String),
    Success,
    Failure { message: String, location: String },
    Unhandled
}

/// A function that takes as input the test file path and its content,
/// and returns the result of running the test on it
type TestFn = Box<dyn Fn(&str) -> TestResult>;

pub struct Test {
    /// test name
    pub name: String,
    /// test function
    pub test: TestFn,
}

pub struct Tester {
    tests: Vec<Test>,
}

impl Tester {
    pub fn new() -> Tester {
        Tester {
            tests: vec![],
        }
    }

    pub fn add_test<T, F>(&mut self, name: &str, test: F)
    where
        T: 'static + DeserializeOwned + UnwindSafe,
        F: Fn(T) + UnwindSafe + RefUnwindSafe + 'static,
    {
        let test_fn = move |input: &str| match parse_as::<T>(&input) {
            Ok(test_case) => Tester::capture_test(|| {
                test(test_case);
            }),
            Err(e) => TestResult::ParseError(e.to_string()),
        };
        self.tests.push(Test {
            name: name.to_string(),
            test: Box::new(test_fn),
        });
    }

    pub fn run_on(&mut self, input: &str) -> TestResult {
        for Test { name, test } in &self.tests {
            match test(input) {
                TestResult::ParseError(_) => {
                    continue;
                }
                res => return res,
            }
        }
        TestResult::Unhandled
    }

    fn capture_test<F>(test: F) -> TestResult
    where
        F: FnOnce() + UnwindSafe,
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
        let result = panic::catch_unwind(|| test());
        panic::set_hook(old_hook);
        match result {
            Ok(_) => TestResult::Success,
            Err(_) => (*test_result.lock().unwrap()).clone(),
        }
    }
}



#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Deserialize)]
    pub struct MyTest {
        pub name: String
    }

    fn fails(_: String) {
        assert!(false);
    }

    fn succeeds(t: MyTest) {
        assert!(t.name == "my_test", "got {}", t.name);
    }

    #[test]
    fn test() {
        let mut tester = Tester::new();
        tester.add_test("fails", fails);
        tester.add_test("succeeds", succeeds);
        let res = tester.run_on("");
        assert!(res == TestResult::Unhandled);
        let res = tester.run_on("{\"name\": \"my_test\"}");
        assert!(res == TestResult::Success);
    }

}
