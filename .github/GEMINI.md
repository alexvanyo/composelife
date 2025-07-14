# Directory: .github

This directory contains configurations for GitHub-specific features, primarily CI/CD workflows.

## Purpose & Contents

- **`workflows/`**: This directory holds the [GitHub Actions](https://docs.github.com/en/actions) workflow definitions for the project.
  - **`auto-update.yml`**: This workflow auto-rebases PRs, to ensure that they can always cleanly merge onto main with a rebase merge.
  - **`baseline-profile.yml`**: This workflow is responsible for generating and updating Android Baseline Profiles, which are crucial for application performance. It runs on every PR merge.
  - **`ci.yml`**: This is the main Continuous Integration workflow. It runs on every push and pull request to build the project, run tests (unit and screenshot), and perform static analysis (like Detekt).
  - **`clear-caches.yml`**: This workflow provides a way to manually or automatically clear caches used by GitHub Actions, which can be useful for resolving build issues.
- **`ci-gradle.properties`**: This file contains Gradle properties that are specific to the CI environment, allowing for different configurations when building on GitHub Actions compared to local development.
