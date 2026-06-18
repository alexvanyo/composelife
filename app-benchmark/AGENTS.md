# Module: app-benchmark

This module contains **Macrobenchmarks** for the main `:app` module.

## Purpose & Architecture

- This module uses the `androidx.benchmark.macro` library to measure the performance of the application as a whole.
- Macrobenchmarks test realistic user journeys, such as startup time, scrolling performance, and navigation.
- These tests run on a real device or emulator and provide more accurate performance metrics than microbenchmarks for end-user-facing interactions.
- The benchmarks in this module are used to validate the effectiveness of performance optimizations, such as the Baseline Profile.

## Usage

- To run these benchmarks, you need to use a specific Gradle command that enables the `staging` build type and sets the `com.alexvanyo.composelife.runBenchmarks` property to `true`.
- The results of these benchmarks are used to track performance over time and catch regressions.

## Key Dependencies

- `androidx.benchmark.macro.junit4`: The core library for writing macrobenchmarks.
