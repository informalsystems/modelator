import os
from modelator.check import check_apalache


def _matchingCheckValue(samplesDirectory, expectedResult: bool, msgEmpty: bool):
    model_files = [filename for filename in os.listdir(samplesDirectory) if filename.split('.')[-1]=="tla"]
    for filename in model_files:
        f = os.path.join(samplesDirectory, filename)
        tla_file_content = open(f).read()

        cfg_filename = filename.split('.')[0] + ".cfg"
        f = os.path.join(samplesDirectory, cfg_filename)
        cfg_file_content = open(f).read()

        res, msg, cex = check_apalache(tla_file_content=tla_file_content, cfg_file_content=cfg_file_content)
        assert res == expectedResult
        if msgEmpty is True:
            assert msg == ""
        else:
            assert len(msg) > 0


def test_check_with_cfg():
    correctSamples = os.path.abspath("tests/sampleFiles/check/correct")
    _matchingCheckValue(correctSamples, True, True)

    flawedSamples = os.path.abspath("tests/sampleFiles/check/flawed")    
    _matchingCheckValue(flawedSamples, False, False)


def test_check_no_cfg():
    tla_file_content = open("tests/sampleFiles/check/Hello.tla").read()

    args = {}
    args["init"] = "InitA"
    args["next"] = "Next"
    args["inv"] = "Inv"

    res, msg, cex = check_apalache(tla_file_content=tla_file_content, apalache_args=args)
    assert res == False

    args["init"] = "InitB"
    res, msg, cex = check_apalache(tla_file_content=tla_file_content, apalache_args=args)
    assert res == True

    args["init"] = "InitC"
    res, msg, cex = check_apalache(tla_file_content=tla_file_content, apalache_args=args)
    assert res == True



