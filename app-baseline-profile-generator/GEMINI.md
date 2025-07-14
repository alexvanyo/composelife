# Module: app-baseline-profile-generator

This module is responsible for generating the **Baseline Profile** for the main `:app` module.

## Purpose & Architecture

- This module uses the `androidx.baselineprofile` Gradle plugin to generate a profile of classes and methods used during critical user journeys.
- The generated profile (`baseline-prof.txt`) is then included in the `:app` module to be packaged with the release app.
- The Android runtime uses this profile to pre-compile the specified code, significantly improving application performance, especially startup time and reducing jank.

## Usage

- The tests in this module define the critical user journeys to be profiled (e.g., starting the app, navigating to a screen).
- These tests are not for verifying correctness, but for exercising the code paths that should be optimized.
- The CI is configured to run these tests and automatically generate and commit the updated baseline profile. You should not need to run this locally.
