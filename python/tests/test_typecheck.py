import os
from modelator.typecheck import typecheck


def _matchingParseValue(samplesDirectory, expectedResult: bool, msgEmpty: bool):
    for filename in os.listdir(samplesDirectory):
        f = os.path.join(samplesDirectory, filename)
        tla_file_content = open(f).read()
        res, msg = typecheck(tla_file_content=tla_file_content)
        assert res == expectedResult
        if msgEmpty is True:
            assert msg == ""
        else:
            assert len(msg) > 0


def test_parse():
    correctSamples = os.path.abspath("tests/sampleFiles/correct")
    _matchingParseValue(correctSamples, True, True)

    flawedSamples = os.path.abspath("tests/sampleFiles/typecheck")    
    _matchingParseValue(flawedSamples, False, False)
