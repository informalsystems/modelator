# HanoiTower in Modelator

## Directory structure

### `/hanoi`

Contains the python code for SUT.

### `/model`

Contains the reference TLA+ model of the SUT.

### `/tests`

Tests written using `modelator` library.

The example test should give an idea of how to use modelator as a model-based-testing or MBT library.

### `/traces`

Contains generated traces from TLA+ model via `modelator` executable.

## Code instruction

Generate traces from TLA+ model using `modelator` executable.

```
modelator sample --model-path model/hanoi.tla --tests Test --traces-dir traces
```

Execute the test using `pytest`.

```
python -m pytest -s
```
