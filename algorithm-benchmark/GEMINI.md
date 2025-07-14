# Module: algorithm-benchmark

This module contains microbenchmarks for the `:algorithm` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform module configured as an Android Application for running benchmarks.
- It uses `androidx.benchmark.micro.junit4` to measure the performance of the core Game of Life algorithms and data structures defined in the `:algorithm` module.
- These benchmarks are crucial for evaluating the performance implications of changes to the simulation logic.

## Usage

- The benchmarks in this module are run on an Android device or emulator.

## Key Dependencies

- `:algorithm`: The module being benchmarked.
- `androidx.benchmark.micro.junit4`: The core library for writing microbenchmarks.
- `:dispatchers-test`: Used to provide test dispatchers for consistent and deterministic testing of coroutine-based code.
- `:patterns`: Used to provide the cell patterns for the benchmarks.

See the [README.md](README.md) for more information.
