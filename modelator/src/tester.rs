use crate::util::*;
use serde::de::DeserializeOwned;
use serde_json::Value;
use std::{any::Any, panic::{self, UnwindSafe, AssertUnwindSafe}, sync::{Arc, Mutex}};

#[derive(Debug, Clone, PartialEq)]
pub enum TestResult {
    Success,
    Failure { message: String, location: String },
    Unhandled
}

pub struct Test<'a> {
    pub name: String,
    pub test: Box<dyn FnMut(& dyn Any) -> TestResult + 'a>,
}

pub struct Tester<'a> {
    tests: Vec<Test<'a>>,
}

impl<'a> Tester<'a> {
    pub fn new() -> Tester<'a> {
        Tester {
            tests: vec![],
        }
    }

    pub fn add_test<T, F>(&mut self, name: &str, mut test: F)
    where
        T: 'static + DeserializeOwned + UnwindSafe + Clone,
        F: FnMut(T)  + 'a,
    {
        let test_fn = move |input: &dyn Any| 
            if let Some(test_case) = input.downcast_ref::<T>() {
                Tester::capture_test(|| {
                    test(test_case.clone());
                })
            }
            else if let Some(input) = input.downcast_ref::<String>() {
                match parse_from_str::<T>(input) {
                    Ok(test_case) => Tester::capture_test(|| {
                        test(test_case.clone());
                    }),
                    Err(_) => TestResult::Unhandled,
                }
            }
            else if let Some(input) = input.downcast_ref::<Value>() {
                match parse_from_value::<T>(input.clone()) {
                    Ok(test_case) => Tester::capture_test(|| {
                        test(test_case.clone());
                    }),
                    Err(_) => TestResult::Unhandled,
                }
            }
            else {
                TestResult::Unhandled
            }
        ;
 
        self.tests.push(Test {
            name: name.to_string(),
            test: Box::new(test_fn),
        });
    }

    pub fn test(&mut self, input: &dyn Any) -> TestResult {
        for Test { test, .. } in &mut self.tests {
            match test(input) {
                TestResult::Unhandled => {
                    continue;
                }
                res => return res,
            }
        }
        TestResult::Unhandled
    }    

    fn capture_test<F>(mut test: F) -> TestResult
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
        let result = panic::catch_unwind(
            AssertUnwindSafe(|| test())
        );
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

    #[test]
    fn test() {
        let mut tester = Tester::new();
        tester.add_test("fails", fails);
        tester.add_test("succeeds_if_my_test", succeeds_if_my_test);

        let res = tester.test(&"".to_string());
        assert!(res == TestResult::Unhandled);

        let data = String::from("{\"name\": \"test\"}");
        let res = tester.test(&data);
        assert!(matches!(res, TestResult::Failure { message, location: _ } if message == "got test"));

        let data = MyTest { name: "my_test".to_string() };
        let res = tester.test(&data);
        assert!(res == TestResult::Success);
        
        let data = String::from("{\"name\": \"my_test\"}");
        let res = tester.test(&data);
        println!("{:?}", res);
        assert!(res == TestResult::Success);

        let data: Value = serde_json::from_str(&data).unwrap();
        let res = tester.test(&data);
        assert!(res == TestResult::Success);

    }

}
