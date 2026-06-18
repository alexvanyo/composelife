# Module: preferences-proto

This module defines the Protocol Buffer schemas for the application's preferences.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It uses the [Wire](https://square.github.io/wire/) library to define the data format for preferences stored in Jetpack Proto DataStore.
- The `.proto` files defining the schema are located in `src/commonMain/proto`.
- The Wire Gradle plugin generates Kotlin data classes from these schema definitions during the build process.
- These generated classes provide a type-safe way to read and write preferences.

## Usage

- When you need to add or change a user preference, you should modify the `.proto` schema in this module.
- The `:preferences` module depends on this module to get access to the generated Kotlin classes for use with DataStore.

## Key Dependencies

- `com.squareup.wire:wire-runtime`: The runtime library for Wire.
- `com.squareup.wire:wire-gradle-plugin`: The Gradle plugin for code generation.
