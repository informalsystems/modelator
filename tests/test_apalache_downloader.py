import os
import subprocess

import appdirs
import pytest

from modelator import const_values
from modelator.utils.modelator_helpers import check_for_apalache_jar


@pytest.mark.network
def test_downloading():
    # first, create a temp directory (that will be removed fully at the end of the test)
    test_download_path = os.path.join(
        appdirs.user_data_dir(__package__), "test", "checkers"
    )
    subprocess.run(["rm", "-rf", test_download_path])
    subprocess.run(["mkdir", "-p", test_download_path])
    jar_path = os.path.join(
        test_download_path,
        "apalache",
        "lib",
        const_values.DEFAULT_APALACHE_JAR_FILENAME,
    )

    # first, try to run Apalache from this directory
    with pytest.raises(Exception):
        subprocess.check_output(["java", "-jar", jar_path, "version"])

    # then, invoke the downloading process and make sure it downloads

    desired_version = "0.25.10"
    downloaded_new_jar = check_for_apalache_jar(
        download_location=test_download_path,
        jar_path=jar_path,
        expected_version=desired_version,
    )
    assert downloaded_new_jar is True

    # now, again try to run Apalache from this directory and make sure it returns the correct version
    version = subprocess.check_output(
        ["java", "-jar", jar_path, "version"], text=True
    ).strip()

    assert version == desired_version

    # knowing that we have a working version, try to download again (it is expected that now download is NOT needed)
    downloaded_new_jar = check_for_apalache_jar(
        download_location=test_download_path,
        jar_path=jar_path,
        expected_version=desired_version,
    )
    assert downloaded_new_jar is False

    # download a different version, but with a wrong checksum
    with pytest.raises(AssertionError):
        _ = check_for_apalache_jar(
            download_location=test_download_path,
            jar_path=jar_path,
            expected_version="0.25.1",
            sha256_checksum=const_values.APALACHE_SHA_CHECKSUMS["0.25.0"],
        )

    # download again, using the proper checksum
    downloaded_new_jar = check_for_apalache_jar(
        download_location=test_download_path,
        jar_path=jar_path,
        expected_version="0.25.1",
    )
    assert downloaded_new_jar is True

    # now, try to download a version for which no checksum is provided
    with pytest.raises(ValueError):
        _ = check_for_apalache_jar(
            download_location=test_download_path,
            jar_path=jar_path,
            expected_version="0.25.2",
        )

    # finally, remove the intermediate directory
    subprocess.run(["rm", "-rf", test_download_path])
