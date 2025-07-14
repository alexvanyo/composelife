# Module: test-activity

This is a Kotlin Multiplatform library module that provides a basic, empty `Activity` for use in Android
instrumentation tests.

## Purpose & Architecture

- The primary purpose of this module is to provide a host `Activity` that can be launched during instrumentation tests.
- This is essential for any test that requires a UI context, such as tests for Compose components, view models, or any code that interacts with the Android framework.
- Other modules' `androidTest` source sets depend on this module to have a reliable, minimal `Activity` to run against.

## Usage

- When writing an instrumentation test that needs to display UI, configure the test to use `TestActivity` as its component.
- This avoids the need to use the main application's `Activity`, which may have complex dependencies and setup that are undesirable in a controlled test environment.
