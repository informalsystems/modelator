# modelator
_<sup>but in Golang<sup>_

[![GitHub go.mod Go version](https://img.shields.io/github/go-mod/go-version/informalsystems/modelator?filename=go%2Fgo.mod)](https://github.com/informalsystems/modelator/tree/main/go)
[![Go project version](https://badge.fury.io/go/github.com%2Finformalsystems%2Fmodelator%2Fgo.svg)](https://badge.fury.io/go/github.com%2Finformalsystems%2Fmodelator%2Fgo)
[![License](https://img.shields.io/github/license/informalsystems/modelator)](https://github.com/informalsystems/modelator/tree/main/go/LICENSE)</br>
[![Go Reference](https://pkg.go.dev/badge/github.com/informalsystems/modelator/go.svg)](https://pkg.go.dev/github.com/informalsystems/modelator/go)
[![Status](https://github.com/informalsystems/modelator/actions/workflows/golang.yml/badge.svg)](https://github.com/informalsystems/modelator/actions/workflows/golang.yml)
[![Go Report Card](https://goreportcard.com/badge/github.com/informalsystems/modelator/go)](https://goreportcard.com/report/github.com/informalsystems/modelator/go)

---
### Instruction
```sh
git clone git@github.com/informalsystems/modelator
cd golang
# Test all examples
go test -v ./examples/...
```

### Example
[Golang port](examples/numbersystem) of [NumberSystem](../rust/tests/integration/resource/numbers.rs)

```sh
# Test NumberSystem example
go test -v ./examples/numbersystem
```

##### Output
```sh
=== RUN   TestFixedExecutions
=== RUN   TestFixedExecutions/test_0
=== RUN   TestFixedExecutions/test_1
--- PASS: TestFixedExecutions (0.00s)
    --- PASS: TestFixedExecutions/test_0 (0.00s)
    --- PASS: TestFixedExecutions/test_1 (0.00s)
=== RUN   TestModelBased
2022/01/20 16:50:36 Generating traces using Modelator cgo-binding...
=== RUN   TestModelBased/[test:_AMaxBMaxTest,_trace:_0]
=== RUN   TestModelBased/[test:_AMaxBMinTest,_trace:_0]
=== RUN   TestModelBased/[test:_AMinBMaxTest,_trace:_0]
--- PASS: TestModelBased (2.92s)
    --- PASS: TestModelBased/[test:_AMaxBMaxTest,_trace:_0] (0.00s)
    --- PASS: TestModelBased/[test:_AMaxBMinTest,_trace:_0] (0.00s)
    --- PASS: TestModelBased/[test:_AMinBMaxTest,_trace:_0] (0.00s)
PASS
ok  	github.com/informalsystems/modelator/examples/numbersystem	2.923s
```
