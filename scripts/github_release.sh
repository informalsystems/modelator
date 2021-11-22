#!/usr/bin/env bash

set -euo pipefail
set -o xtrace

# the `[release] vX.Y.Z` is merged to `main` now

# create a tag `vX.Y.Z`

TAG_NAME="v${RELEASE_VERSION}"

rm -rf ".changelog/unreleased"
mv ".changelog/v${RELEASE_VERSION}" ".changelog/unreleased"

RELEASE_NOTES_FILE="current_changelog"

unclog build -u | tail -n +3 > "$RELEASE_NOTES_FILE"

git tag -a "$TAG_NAME" -F "$RELEASE_NOTES_FILE"
git push --tags

# create a github release with change log

gh release create \
    --title "$TAG_NAME" \
    --notes-file "$RELEASE_NOTES_FILE" \
    "$TAG_NAME"
    # ./dist/*.tar.gz
    # ./dist/*.zip

# publish to crates.io, pypi.org and go registry
# done on GH action workflow
