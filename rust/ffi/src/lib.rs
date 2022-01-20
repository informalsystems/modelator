use std::collections::BTreeMap;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

pub fn generate_json_traces_from_tla_tests(
    tla_tests_file_path: &str,
    tla_config_file_path: &str,
) -> Result<String, anyhow::Error> {
    let runtime = modelator::ModelatorRuntime::default();
    let trace_results = runtime.traces(tla_tests_file_path, tla_config_file_path)?;
    let trace_results = trace_results
        .into_iter()
        .map::<Result<_, anyhow::Error>, _>(|(testname, traces)| {
            let traces = traces?;
            Ok((
                testname,
                traces
                    .into_iter()
                    .map(|trace| trace.into_iter().collect::<Vec<_>>())
                    .collect::<Vec<_>>(),
            ))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    Ok(serde_json::to_string_pretty(&trace_results)?)
}

#[repr(C)]
pub struct CResult {
    data: *mut c_char,
    error: *mut c_char,
}

impl<R, E> From<Result<R, E>> for CResult
where
    R: ToString,
    E: ToString,
{
    fn from(result: Result<R, E>) -> Self {
        match result {
            Ok(ok) => Self {
                data: CString::new(ok.to_string()).unwrap().into_raw(),
                error: std::ptr::null_mut(),
            },
            Err(error) => Self {
                data: std::ptr::null_mut(),
                error: CString::new(error.to_string()).unwrap().into_raw(),
            },
        }
    }
}

#[no_mangle]
/// # Safety
///
/// Dereference raw pointer arguments
pub unsafe extern "C" fn generate_json_traces_from_tla_tests_rs(
    tla_tests_file_path_c: *const c_char,
    tla_config_file_path_c: *const c_char,
) -> CResult {
    let (tla_tests_file_path, tla_config_file_path) = (
        CStr::from_ptr(tla_tests_file_path_c),
        CStr::from_ptr(tla_config_file_path_c),
    );
    generate_json_traces_from_tla_tests(
        tla_tests_file_path.to_str().unwrap(),
        tla_config_file_path.to_str().unwrap(),
    )
    .into()
}
