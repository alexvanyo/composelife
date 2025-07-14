# Module: algorithm

This module contains the core logic for Conway's Game of Life.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It contains the data structures (e.g., `CellState`, `GameOfLifeState`) and the simulation algorithms (e.g., `HashLifeAlgorithm`, `NaiveGameOfLifeAlgorithm`).
- It also handles serialization and deserialization of cell patterns in various formats (like RLE, Plaintext, etc.).

## Source Code Structure

- **The primary, platform-agnostic logic is located in `src/jvmMain/kotlin`**. This is the "common" code for this project.
- Platform-specific implementations or bindings are in other source sets like `src/androidMain` and `src/desktopMain`.
- When adding new core algorithm logic, it should almost always be placed in `src/jvmMain/kotlin`.
- Code in `src/jvmMain/kotlin` should be pure Kotlin and must not depend on any platform-specific APIs (like the Android SDK).

## Key Considerations

- **Performance is critical.** The algorithms in this module are computationally intensive. Be mindful of performance and memory allocations when making changes.
- **Testing is extensive.** This module has a rich set of tests in various test source sets (`jvmTest`, `androidUnitTest`, etc.). Ensure any new logic is thoroughly tested.
