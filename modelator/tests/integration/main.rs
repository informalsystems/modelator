use serde::Deserialize;
use serde_json::Error;
use std::path::PathBuf;
use std::{fs, path::Path};

static ROOT_DIR: &str = "tests/integration";

#[test]
/// This is the single, master, integration test
fn integration_test() {
    // We follow the approach proposed in the following link for integration tests:
    // https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html
    // TLDR: use 1 integration test in tests/integration/

    match load_test_batches() {
        Ok(batches) => batches.iter().for_each(|batch| {
            for test in batch.tests.iter() {
                if let Err(e) = run_single_test(test) {
                    panic!(
                        r#"Test batch {} failed.
[name:{},description:{}]
Error: 
{}
"#,
                        batch.name, e, batch.name, batch.description
                    )
                }
            }
        }),
        Err(e) => panic!("{}", e),
    }
}

fn run_single_test(test: &Test) -> Result<(), Error> {
    Ok(())
}

#[derive(Debug, Deserialize)]
struct Test {}

#[derive(Debug, Deserialize)]
struct TestBatch {
    name: String,
    description: String,
    tests: Vec<Test>,
}

impl TestBatch {
    fn load(filename: &str) -> Result<TestBatch, serde_json::Error> {
        let path = PathBuf::new()
            .join(ROOT_DIR)
            .join("resource")
            .join(filename);
        let content = fs::read_to_string(path)
            .expect(&format!("Unable to read contents of a {} file", filename).to_owned());
        let ret: TestBatch = serde_json::from_str(&content)?;
        return Ok(ret);
    }
}

type TestBatchName = String;

#[derive(Debug, Deserialize)]
struct TestBatchList {
    filenames: Vec<TestBatchName>,
}

impl TestBatchList {
    fn load() -> Result<TestBatchList, serde_json::Error> {
        let path = PathBuf::new().join(ROOT_DIR).join("test_batch_list.json");
        let content = fs::read_to_string(path)
            .expect("Unable to read contents of a test_batch_list.json file");
        let ret: TestBatchList = serde_json::from_str(&content)?;
        return Ok(ret);
    }
}

fn load_test_batches() -> Result<Vec<TestBatch>, serde_json::Error> {
    let test_batch_list = TestBatchList::load()?;

    let mut ret: Vec<TestBatch> = Vec::new();

    for filename in test_batch_list.filenames.iter() {
        ret.push(TestBatch::load(filename)?);
    }
    Ok(ret)
}
