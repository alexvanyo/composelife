# Module: kmp-android-runner

This module provides a custom test runner for Kotlin Multiplatform projects, enabling shared test logic to be executed on Android.

## Purpose & Architecture

- This is a Kotlin Multiplatform library that contains a custom JUnit test runner.
- Its primary goal is to allow test classes written in common source sets (like `commonTest` or `jbTest`) to be correctly discovered and executed by the standard Android instrumentation test runner.
- This is a foundational component of the project's hierarchical testing strategy, enabling maximum code reuse for test logic.

## Usage

- Test classes in `commonTest` or other shared source sets that are intended to run on Android should be annotated in a way that this runner can discover them.
- The `testInstrumentationRunner` property in the `build.gradle.kts` of modules with instrumentation tests is likely configured to use a runner from this module (or one that delegates to it, like `InjectTestRunner`).
