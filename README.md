# Modelator

| ⚠️ We are working on a new and entirely reworked Modelator architecture for improved performance and interoperability. Therefore, the current version is not maintained. The reworked version will be released in Q3 2022. ⚠️ |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Release](https://img.shields.io/github/v/release/informalsystems/modelator?sort=semver&include_prereleases)](https://github.com/informalsystems/modelator/releases)
[![Build Status](https://github.com/informalsystems/modelator/actions/workflows/python.yml/badge.svg)](https://github.com/informalsystems/modelator/actions/workflows/python.yml)

This repository contains the source code for `modelator` - a framework and tools for model-based testing.

_We deprecated `modelator` support for Rust and Go. `modelator` is used as a python package._

# Instruction

To install `modelator` via `pip`, execute the following

```sh
# over https
pip install git+https://github.com/informalsystems/modelator
# or, over ssh
pip install git+ssh://git@github.com/informalsystems/modelator
python
...
>>> import modelator
```

If you are using a Poetry project, execute the following to add `modelator` as a dependency,

```sh
# over https
poetry add git+ssh://git@github.com/informalsystems/modelator#dev # `poetry` assumes `master` as default branch
# or, over ssh
poetry add git+https://github.com/informalsystems/modelator#dev
```

## Contributing

If you wish to contribute to `modelator`, set up the repository as follows,

```
git clone git@github.com/informalsystems/modelator
cd modelator
poetry install
poetry shell
```

## License

Copyright © 2021-2022 Informal Systems Inc. and modelator authors.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use the files in this repository except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
