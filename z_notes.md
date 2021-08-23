#

# Commands

```
apalache
    # (suddenly started working)
    parse
        # generated a <filename>Parsed.tla file, not sure what it's for
    test
        # think this is the same as for _tlc_ cmd but mine panicked for the example I gave it
tla
    generate-tests
        # takes a .tla and .cfg file for the MBT _tests_, which extend the model. The tests are just assertions
        # converts (each test within) into a form which is directly runnable by TLC/(apalache?)
        # named something like
        # <filename>_<testname>.tla
        # <filename>_<testname>.cfg
    tla-trace-to-json-trace
        # converts .tla traces to json traces
tlc
    test
        # takes a .tla and .cfg file as generated using 'tla generate-tests <.tla> <.cfg>
        # and runs it using tlc to get a .tla trace for the given test
```