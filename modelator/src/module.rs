use crate::{Artifact, ArtifactManifest};
use paste::paste;
use serde::{Deserialize, Serialize};
use serde_json;

#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct ModuleManifest {
    pub name: &'static str,
    pub description: &'static str,
    pub version: &'static str,
    pub methods: Vec<MethodManifest>,
}

// For static manifests of modules in Rust
impl From<&'static str> for ModuleManifest {
    fn from(json: &'static str) -> ModuleManifest {
        serde_json::from_str(json).unwrap()
    }
}

#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct MethodManifest {
    pub name: &'static str,
    pub description: &'static str,
    pub inputs: Vec<ArtifactManifest>,
    pub results: Vec<ArtifactManifest>,
    pub errors: Vec<ArtifactManifest>,
}

pub trait Module {
    fn manifest() -> ModuleManifest;
    fn manifest_json() -> String {
        serde_json::to_string_pretty(&Self::manifest()).unwrap()
    }

    //fn run(&self, method: &str, inputs: Vec<Box<dyn Artifact>>) -> Result<Vec<Box<dyn Artifact>>, Vec<Box<dyn Artifact>>>;
}

pub trait Method {
    fn manifest() -> MethodManifest;
    fn run(
        &self,
        method: &str,
        inputs: Vec<Box<dyn Artifact>>,
    ) -> Result<Vec<Box<dyn Artifact>>, Vec<Box<dyn Artifact>>>;
}

// A macro for constructing modules
#[macro_export]
macro_rules! module {
    (   $name:ident( $descr:expr, $version:expr )
        methods( $( $method:ident),* )
    ) => {
        paste! {
            impl Module for $name {
                fn manifest() -> ModuleManifest {
                    ModuleManifest {
                        name: stringify!($name),
                        description: $descr,
                        version: $version,
                        methods: vec![$(
                            $name::[<$method _manifest>]()
                        ),* ],
                    }
                }
            }
        }
    }
}

// A macro for constructing module methods
#[macro_export]
macro_rules! method {
    (   $module:ident.$name:ident($descr:expr)
        inputs( $( $input:ident : $input_t:ty),* )
        results( $( $result:ident : $result_t:ty),* )
        errors( $( $error:ident : $error_t:ty),* )
        $b:block
    ) => {
        paste! {
            impl $module {
                pub fn $name(&self, $($input: $input_t),*)
                    -> Result<($($result_t),*), ($($error_t),*)>
                    $b

                pub fn [<$name _manifest>]() -> MethodManifest {
                    MethodManifest {
                        name: stringify!($name),
                        description: $descr,
                        inputs: vec![$(
                            ArtifactManifest {
                                name: stringify!($input),
                                typ: stringify!($input_t),
                            }
                        ),* ],
                        results: vec![$(
                            ArtifactManifest {
                                name: stringify!($result),
                                typ: stringify!($result_t),
                            }
                        ),* ],
                        errors: vec![$(
                            ArtifactManifest {
                                name: stringify!($error),
                                typ: stringify!($error_t),
                            }
                        ),* ],
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub struct Model {}
    pub struct ModelConfig {}
    pub struct Test {}
    pub struct Trace {}
    pub struct Log {}

    pub struct TLC {}

    module! {
        TLC("TLC model checker", "1.0")
        methods(test)
    }

    method! {
        TLC.test("Run TLC model checker on the given model, config, and test, and produce a trace for them")
        inputs(model: Model, config: ModelConfig, test: Test)
        results(trace: Trace)
        errors(message: String, output: Log)
        {
            Err(("not implemented".to_string(), Log{}))
        }
    }

    #[test]
    fn module_manifest() {
        assert_eq!(
            TLC::manifest(),
            serde_json::from_str(r#"{
                "name": "TLC",
                "description": "TLC model checker",
                "version": "1.0",
                "methods": [
                {
                    "name": "test",
                    "description": "Run TLC model checker on the given model, config, and test, and produce a trace for them",
                    "inputs": [
                    {
                        "name": "model",
                        "type": "Model"
                    },
                    {
                        "name": "config",
                        "type": "ModelConfig"
                    },
                    {
                        "name": "test",
                        "type": "Test"
                    }
                    ],
                    "results": [
                    {
                        "name": "trace",
                        "type": "Trace"
                    }
                    ],
                    "errors": [
                    {
                        "name": "message",
                        "type": "String"
                    },
                    {
                        "name": "output",
                        "type": "Log"
                    }
                    ]
                }
                ]
            }
            "#).unwrap());
    }
}
