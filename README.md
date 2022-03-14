# Modelator

|⚠️ We are working on a new and entirely reworked Modelator architecture for improved performance and interoperability. Therefore, the current version is not maintained. The reworked version will be released in Q2 2022. ⚠️|
|-|

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Crates.io Version](https://img.shields.io/crates/v/modelator.svg)](https://crates.io/crates/modelator)
[![Docs.rs](https://docs.rs/modelator/badge.svg)](https://docs.rs/modelator)
[![Release](https://img.shields.io/github/v/release/informalsystems/modelator?sort=semver&include_prereleases)](https://github.com/informalsystems/modelator/releases)

The framework and tools for model-based testing.

This (mono-)repository contains the source code for `modelator`.
- [`rust`](rust) directory contains the source code for the core library, cli app and C library via FFI.
- [`golang`](golang) directory contains the golang module using C library via FFI.
- [`python`](python) directory contains the python code to fetch assets to set up `modelator` for the first time.

## Usage

There are two ways to use `modelator` - as a cli app or as a library.

### CLI

The latest release,
```
cargo install modelator
```

The `main` branch,
```
cargo install --git https://github.com/informalsystems/modelator
```

Make sure `$HOME/.cargo/bin` is added to your system path. Check the `modelator --help` for usage instructions.

### Library

Currently we support [`rust`](rust) and [`golang`](golang) libraries. Please refer to the `README.md`s at [`rust`](rust/README.md) and [`golang`](golang/README.md) directories for more details.

## Resources

Currently it is possible to view the docs book only if [mdBook](https://github.com/rust-lang/mdBook) is installed. Then the book can be viewed by navigating to `docs/`, running `mdbook serve` and then navigating to `localhost:3000` in your browser.

## Contributing

Coming soon!

## License

Copyright © 2021 Informal Systems Inc. and modelator authors.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use the files in this repository except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
