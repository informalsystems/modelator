import subprocess
import pytest
from modelator.utils.modelator_helpers import check_for_apalache_jar
import appdirs
import os


@pytest.mark.network
def test_downloading():
    # first, create a temp directory (that will be removed fully at the end of the test)
    test_download_path = os.path.join(
        appdirs.user_data_dir(__package__), "test", "checkers"
    )
    subprocess.run(["mkdir", "-p", test_download_path])
    jar_path = os.path.join(test_download_path, "apalache", "lib", "apalache.jar")

    # first, try to run Apalache from this directory
    with pytest.raises(Exception):
        subprocess.run(
            ["java", "-jar", jar_path, "version"],
            stdout=subprocess.PIPE,
            check=True,
        )

    # then, invoke the downloading process and make sure it downloads

    desired_version = "0.25.0"
    downloaded_new_jar = check_for_apalache_jar(
        download_location=test_download_path, jar_path=jar_path
    )
    assert downloaded_new_jar is True

    # now, again try to run Apalache from this directory and make sure it returns the correct version
    out = subprocess.run(
        ["java", "-jar", jar_path, "version"],
        stdout=subprocess.PIPE,
        check=True,
    )
    version = out.stdout.decode("utf-8").strip()
    assert version == desired_version

    # knowing that we have a working version, try to download again (it is expected that now download was needed)
    downloaded_new_jar = check_for_apalache_jar(
        download_location=test_download_path, jar_path=jar_path
    )
    assert downloaded_new_jar is False

    # finally, download again, but a different version (and now it should download again)
    downloaded_new_jar = check_for_apalache_jar(
        download_location=test_download_path,
        jar_path=jar_path,
        expected_version="0.25.1",
    )
    assert downloaded_new_jar is True

    # finally, remove the intermediate directory
    subprocess.run(["rm", "-r", test_download_path])
