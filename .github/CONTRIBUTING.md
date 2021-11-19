# Contributing

Thank you for your interest in contributing to our project.

## Branches

All significant changes must be done on a new branch and creating PRs.
The `main` branch is modified only through PRs.

## Forking

If you want to contribute, but do not have write permission, the contribution must be made through a fork on Github.

## Reporting bugs

When reporting bugs, search among existing issues first - even among closed issues.
If you found one exisiting issues, do comment with the details of your own bug.
So that we are aware of number of people affected by that bug.

If you can not find an issue, thank you for finding a new issue.
Please go ahead open a new issue with details.

## Pull request

Every pull request must correspond to an issue.

Before opening a pull request, open an issue describing what is wrong and what is your solution.
Then, reference it in your PR with the changes for the solution.

Do not forget to include `CHANGELOG.md` changes if applicable.

## Changelog

We maintain our changelog using [`unclog`](https://github.com/informalsystems/unclog).

Every non-trivial PR must add an entry(ies) to `.changelog` directory using `unclog add`.
This will add the entries to `unreleased` changes.

When a release is prepared, the unrelease changes must be moved to `release` using `unclog release`.

## Release

We follow [_Semantic Versioning_](http://semver.org) for releases.

When all the code changes are ready and merged to `main`, a `release/vX.Y.Z` branch must be opened from `main`.
All the changes for bumping version numbers and moving unreleased changes via unclog should be committed in this branch.

When `release/vX.Y.Z` is ready with correct version bumps, create a PR and merge it to `main`.
Tag the merge commit with `vX.Y.Z` and prepare a release on Github, publish on package registries for Golang, Rust and Python.

In future, the releases would be done via GH workflow. It must be triggered by tagging a commit with `vX.Y.Z`.
The workflow must contain a check to make sure that everything is ready for release, otherwise fail.

## License

All the contributions must be under `Apache-2.0` license.
