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

### Checklist
- The versions **should not be bumped** from current version. The versions will be bumped by the workflow.
- The changes are added to `.changelog` via `unclog add`.
- Write a summary of the release at `.changelog/unreleased/summary.md`.
- Perform `unclog build -u` to check the latest changelog. Commit changes if something is wrong.
  - This will be used as release notes in PR and Github release.

### Workflow
- When the codebase is ready for a release, trigger the [`Prepare Release` workflow](actions/workflows/prepare-release.yml) from project Actions.
  - We follow [_Semantic Versioning_](http://semver.org). The workflow takes an input - the component of the semantic version to be updated.
    - `patch` (v1.4.2 becomes v1.4.3) _(default)_
    - `minor` (v1.4.2 becomes v1.5.0)
    - `major` (v1.4.2 becomes v2.0.0)
  - The workflow will create a branch `release/vX.Y.Z` from `main`.
  - And commit necessary changes on it for the release.
    - This includes bumping version numbers in projects.
    - Preparing changelog.
    - Publish projects with `--dry-run` to make sure everything is fine locally.
  - Then, create a PR with title `[RELEASE] vX.Y.Z` to `main` branch.
- We review the PR. If something went wrong in the PR, we push changes to the branch to correct them.
- When the PR is ready, we simply merge it to `main`, which triggers the [`Release` workflow](actions/workflows/release.yml).
  - It will tag the merge commit with `vX.Y.Z`.
  - Publish the projects to package registries.
  - Create a Github release with changelog.

## License

All the contributions must be under `Apache-2.0` license.
