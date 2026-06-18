# Module: roborazzi-showkase-screenshot-test

This module is the heart of the project's automated screenshot testing system.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module that targets Android.
- This module uses **Roborazzi** to capture and verify screenshots of Jetpack Compose components.
- It uses **Showkase** to automatically discover all `@Composable` functions annotated with `@Preview` across the entire project.
- The tests in this module iterate through all Showkase-discovered components and generate a Roborazzi screenshot test for each one.
- This provides a comprehensive and automated way to prevent UI regressions.

## Usage

- To add a new screenshot test, you simply need to create a `@Preview`-annotated `@Composable` function for your component in its own module. Showkase and this module will automatically pick it up and test it.
- Screenshots are stored in the module's `build/outputs/roborazzi` directory.
- The CI is configured to automatically update screenshots if changes are detected, so you rarely need to run these tests locally.

## Key Dependencies

- `com.github.takahirom.roborazzi`: The core screenshot testing library.
- `com.airbnb.android:showkase`: For component discovery.
- `org.robolectric`: Roborazzi uses Robolectric to run the tests on the JVM without needing an emulator.
