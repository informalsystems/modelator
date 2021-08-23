#

# Commands

```
apalache
    # (suddenly started working)
    parse
        # generated a <filename>Parsed.tla file, this is just a wrapper around Apalaches parse functionality
        # (used to check spec is syntactically correct)
    test
        # think this is the same as for _tlc_ cmd but mine panicked for the example I gave it
tla
    generate-tests
        # takes a .tla and .cfg file for the MBT _tests_, which extend the model.
        # The tests are just assertions.
        # Converts (each test within) into a form which is directly runnable by TLC/(apalache?)
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

# TODO:

Make subprocesses based on `Command` more flexible (env args)

# Other notes

I added cmd.env pointing to Java zulu to help me debug
