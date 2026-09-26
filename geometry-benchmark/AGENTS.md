# Module: geometry-benchmark

This module contains microbenchmarks for the `:geometry` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform module configured as an Android Application for running benchmarks.
- It uses `androidx.benchmark.micro.junit4` to measure the performance of geometric calculations and cell intersections defined in the `:geometry` module.
- These benchmarks are crucial for evaluating the performance implications of changes to the line segment path rasterization and cell intersection logic.

## Usage

- The benchmarks in this module are run on an Android device or emulator.
- **Build Type Constraints**: Benchmarks must not run as `debug` because debugging options introduce performance overhead. Ensure benchmark configurations use the `staging` build type.
- **Gradle Managed Devices (GMD)**: Instrumented tests for benchmarks run on GMD should specify the test type as `staging` for exact profiling behavior.

## Key Dependencies

- `:geometry`: The module being benchmarked.
- `androidx.benchmark.micro.junit4`: The core library for writing microbenchmarks.

See the [README.md](README.md) for more information.
