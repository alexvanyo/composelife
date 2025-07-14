# Module: ui-common-screenshot-tests

This module contains screenshot tests for the `:ui-common` module.

## Purpose & Architecture

- This is an Android library module.
- It uses Roborazzi to capture and verify screenshots of the Jetpack Compose components defined in the `:ui-common` module.
- This ensures that changes to the common UI components do not cause unintended visual regressions.
- Tests in this module are run on CI to automate the verification process.

## Key Dependencies

- `:ui-common`: The module containing the components under test.
- `com.github.takahirom.roborazzi`: The core screenshot testing library.
- `:test-activity`: To provide an `Activity` context for rendering the Compose UI.
