# Module: patterns

This module contains a collection of pre-defined patterns for Conway's Game of Life.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module that provides a set of well-known Game of Life patterns.
- It depends on the `:algorithm` module to use its data structures (like `CellState`) to represent the patterns.
- It uses a sealed class hierarchy, powered by the `sealed-enum` library, to create a type-safe enumeration of the available patterns.
- This allows the rest of the application to easily access and use these patterns, for example, to populate a list of sample patterns for the user to choose from.
- The module targets both Android and Desktop platforms.

## Key Dependencies

- `:algorithm`: To access the core Game of Life data structures.
- `com.livefront:sealed-enum-runtime`: To generate utilities for the sealed class hierarchy of patterns.
