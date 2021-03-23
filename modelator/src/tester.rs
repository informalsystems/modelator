use crate::util::*;
use serde::de::DeserializeOwned;
use serde_json::Value;
use std::{panic::{self, RefUnwindSafe, UnwindSafe}, sync::{Arc, Mutex}};

#[derive(Debug, Clone, PartialEq)]
pub enum TestResult {
    Success,
    Failure { message: String, location: String },
    Unhandled
}

pub struct Test {
    pub name: String,
    pub test_str: Box<dyn Fn(&str) -> TestResult>,
    pub test_value: Box<dyn Fn(&Value) -> TestResult>,
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
        F: Fn(T) + UnwindSafe + RefUnwindSafe + 'static + Copy,
    {
        let test_str = move |input: &str| match parse_from_str::<T>(&input) {
            Ok(test_case) => Tester::capture_test(|| {
                test(test_case);
            }),
            Err(_) => TestResult::Unhandled,
        };
        let test_value = move |input: &Value| match parse_from_value::<T>(input.clone()) {
            Ok(test_case) => Tester::capture_test(|| {
                test(test_case);
            }),
            Err(_) => TestResult::Unhandled,
        };
 
        self.tests.push(Test {
            name: name.to_string(),
            test_str: Box::new(test_str),
            test_value: Box::new(test_value),
        });
    }

    pub fn run_on_str(&mut self, input: &str) -> TestResult {
        for Test { test_str, .. } in &self.tests {
            match test_str(input) {
                TestResult::Unhandled => {
                    continue;
                }
                res => return res,
            }
        }
        TestResult::Unhandled
    }

    pub fn run_on_value(&mut self, input: &Value) -> TestResult {
        for Test { test_value, .. } in &self.tests {
            match test_value(input) {
                TestResult::Unhandled => {
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

    fn succeeds_if_my_test(t: MyTest) {
        assert!(t.name == "my_test", "got {}", t.name);
    }

    #[test]
    fn test() {
        let mut tester = Tester::new();
        tester.add_test("fails", fails);
        tester.add_test("succeeds_if_my_test", succeeds_if_my_test);

        let res = tester.run_on_str("");
        assert!(res == TestResult::Unhandled);

        let data = "{\"name\": \"test\"}";
        let res = tester.run_on_str(data);
        assert!(matches!(res, TestResult::Failure { message, location: _ } if message == "got test"));

        let data = "{\"name\": \"my_test\"}";
        let res = tester.run_on_str(data);
        assert!(res == TestResult::Success);

        let json: Value = serde_json::from_str(data).unwrap();
        let res = tester.run_on_value(&json);
        assert!(res == TestResult::Success);

    }

}
