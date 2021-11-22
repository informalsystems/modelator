This is the massive refactoring release: all internal and external interfaces has been changed; also the tool stability has been greatly improved.

Improvements:
 - Refactor error handling (#53)
 - Reliable extraction of counterexample traces (#58)
 - Reintroduce generic artifacts (#61)
 - Rework Apalache module (#62)
 - Rework TLC module (#63)

Bug fixes:
 - Confusing "No test trace found" error state (#52)
 - Running binary with only the argument tla causes panic instead of giving warning to user (#55)
 - Translate.tla counterexample using modelator tla tla-trace-to-json-trace <filename> results in parsing error (#56)
