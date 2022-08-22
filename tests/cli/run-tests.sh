#!/usr/bin/env bash

MDX=ocaml-mdx

if ! command -v $MDX &> /dev/null; then
    echo "$MDX could not be found"
    echo "Please install MDX (https://github.com/realworldocaml/mdx)"
    exit 1
fi

eval $(opam env)

test_file() {
    echo "Testing file $1..."
    $MDX test -v $1
    if [ -f "$1.corrected" ]; then
        echo "FAILED: see $1.corrected"
    else
        echo "OK"
    fi
}

for MD_FILE in *.md; do
    test_file $MD_FILE
done
