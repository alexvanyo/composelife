# Module: wear-baseline-profile-generator

This module is responsible for generating the **Baseline Profile** for the `:wear` module.

## Purpose & Architecture

- This module uses the `androidx.baselineprofile` Gradle plugin to generate a profile of classes and methods used during critical user journeys on Wear OS.
- The generated profile (`baseline-prof.txt`) is then included in the `:wear` module to be packaged with the release watch face.
- This significantly improves application performance, especially startup time and reducing jank.

## Usage

- The tests in this module define the critical user journeys to be profiled (e.g., starting the watch face).
- These tests are not for verifying correctness, but for exercising the code paths that should be optimized.
- The CI is configured to run these tests and automatically generate and commit the updated baseline profile.
