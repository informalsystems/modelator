from modelator.utils.apalache_helpers import extract_parse_error, extract_tla_module_name
def test_extract_parse_error():
    parser_output_with_error = {
        r"""
        Parse HelloFlawed.tla                                             I@10:10:01.773
PASS #0: SanyParser                                               I@10:10:01.780
Parsing file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla
***Parse Error***
Was expecting "Identifier"
Encountered "Beginning of definition" at line 11, column 1 and token "," 

Residual stack trace follows:
variable declaration starting at line 5, column 1.
Module body starting at line 5, column 1.
Module definition starting at line 1, column 1.

Error by TLA+ parser: *** Abort messages: 1

In module HelloFlawed

Could not parse module HelloFlawed from file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla


 E@10:10:01.891
It took me 0 days  0 hours  0 min  0 sec                          I@10:10:01.894
Total time: 0.761 sec                                             I@10:10:01.894
EXITCODE: ERROR (255)
        """: r"""Was expecting "Identifier"
Encountered "Beginning of definition" at line 11, column 1 and token "," """,

    r"""
    Output directory: /Users/ivan/Documents/codebase/modelator/python/modelator/samples/_apalache-out/HelloFlawed.tla/2022-05-05T10-18-36_8941582266930709599
Parse HelloFlawed.tla                                             I@10:18:36.938
PASS #0: SanyParser                                               I@10:18:36.953
Parsing file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla
***Parse Error***
Encountered "Beginning of definition" at line 13, column 8 and token "/\\" 

Residual stack trace follows:
ExtendableExpr starting at line 13, column 8.
Expression starting at line 13, column 8.
Junction Item starting at line 13, column 5.
AND-OR Junction starting at line 12, column 5.
ExtendableExpr starting at line 12, column 5.

Error by TLA+ parser: *** Abort messages: 1

In module HelloFlawed

Could not parse module HelloFlawed from file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla


 E@10:18:37.068
It took me 0 days  0 hours  0 min  0 sec                          I@10:18:37.073
Total time: 0.792 sec                                             I@10:18:37.073
EXITCODE: ERROR (255)
""": r"""Encountered "Beginning of definition" at line 13, column 8 and token "/\\"  """,
r"""Output directory: /Users/ivan/Documents/codebase/modelator/python/modelator/samples/_apalache-out/HelloFlawed.tla/2022-05-05T10-20-16_7494950703120125298
Parse HelloFlawed.tla                                             I@10:20:16.759
PASS #0: SanyParser                                               I@10:20:16.775
Parsing file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla
***Parse Error***

  Precedence conflict between ops \lor in block line 24, col 9 to line 24, col 10 of module HelloFlawed and \land.

Residual stack trace follows:
ExtendableExpr starting at line 24, column 16.
ExtendableExpr starting at line 24, column 12.
ExtendableExpr starting at line 22, column 9.
Expression starting at line 22, column 9.
ExtendableExpr starting at line 21, column 5.

Error by TLA+ parser: *** Abort messages: 1

In module HelloFlawed

Could not parse module HelloFlawed from file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla


 E@10:20:16.910
It took me 0 days  0 hours  0 min  0 sec                          I@10:20:16.912
Total time: 0.790 sec                                             I@10:20:16.913
EXITCODE: ERROR (255)
""": r"""Precedence conflict between ops \lor in block line 24, col 9 to line 24, col 10 of module HelloFlawed and \land."""

    }

    parser_output_without_error = [
        r"""Parse Hello.tla                                                   I@10:08:58.160
PASS #0: SanyParser                                               I@10:08:58.167
Parsing file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/Hello.tla
Parsing file /private/var/folders/ws/8cq6ncrs0h91f1tx4pb7tzx80000gn/T/Naturals.tla
Parsing file /private/var/folders/ws/8cq6ncrs0h91f1tx4pb7tzx80000gn/T/FiniteSets.tla
Parsing file /private/var/folders/ws/8cq6ncrs0h91f1tx4pb7tzx80000gn/T/Sequences.tla
Parsed successfully
Root module: Hello with 5 declarations.       I@10:08:58.609
It took me 0 days  0 hours  0 min  1 sec                          I@10:08:58.611
Total time: 1.116 sec                                             I@10:08:58.611
EXITCODE: OK
""",
 "",
 "hello",
 r"""# APALACHE
# version: 0.20.3
# build  : a0ce63e
#
# Usage statistics is ON. Thank you!
# If you have changed your mind, disable the statistics with config --enable-stats=false.

Output directory: /Users/ivan/Documents/codebase/modelator/python/modelator/samples/_apalache-out/Hello.tla/2022-05-05T10-25-49_8775545694601764932
Parse Hello.tla                                                   I@10:25:49.645
PASS #0: SanyParser                                               I@10:25:49.655
Parsing file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/Hello.tla
  > Error parsing file /Users/ivan/Documents/codebase/modelator/python/modelator/samples/Hello.tla E@10:25:49.769
Parser has failed                                                 I@10:25:49.772
It took me 0 days  0 hours  0 min  0 sec                          I@10:25:49.774
Total time: 0.819 sec                                             I@10:25:49.775
EXITCODE: ERROR (255)"""
    ]

    for output in parser_output_with_error:
        assert parser_output_with_error[output].strip() == extract_parse_error(output).strip()

    for output in parser_output_without_error:
        assert extract_parse_error(output) is None

def test_extract_tla_module_name():
    names = {
        "---- MODULE Hello --------":"Hello",
        "----MODULE Hello--------":"Hello",
        "------ MODULE Hello_Hi --------":"Hello_Hi"
    }

    for name in names:
        assert extract_tla_module_name(name) == names[name]