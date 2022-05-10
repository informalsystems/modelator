import os
from modelator.typecheck import typecheck


def _matchingTypecheckValue(samplesDirectory, expectedResult: bool, msgEmpty: bool):
    for filename in os.listdir(samplesDirectory):
        f = os.path.join(samplesDirectory, filename)
        tla_file_content = open(f).read()
        res, msg = typecheck(tla_file_content=tla_file_content)
        assert res == expectedResult
        if msgEmpty is True:
            assert msg == ""
        else:
            assert len(msg) > 0


def test_typecheck():
    correctSamples = os.path.abspath("tests/sampleFiles/typecheck/correct")
    _matchingTypecheckValue(correctSamples, True, True)

    flawedSamples = os.path.abspath("tests/sampleFiles/typecheck/flawed")    
    _matchingTypecheckValue(flawedSamples, False, False)
