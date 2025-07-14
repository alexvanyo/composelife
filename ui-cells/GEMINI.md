# Module: ui-cells

This is a Kotlin Multiplatform library module responsible for the low-level rendering of the Game of Life cell grid.

## Purpose & Architecture

- This module provides a highly specialized `@Composable` function, likely named `CellUniverse`, that can efficiently render a `CellWindow` from the `:algorithm` module.
- It is a core component of the visualization, used by both the `:ui-mobile` and `:ui-wear` modules.
- Given the project's use of advanced rendering, this module may contain custom `Draw` calls or even OpenGL/AGSL/SKSL shaders to render the cells performantly.

## Source Code Structure

- **`jbMain`**: Contains the primary, shared Jetpack Compose implementation of the cell rendering logic.
- **`jvmMain`**: May contain additional JVM-specific logic.
- **`androidMain` / `desktopMain`**: Contain any necessary platform-specific bindings or performance optimizations.

## Key Considerations

- **Performance is critical.** This is the most frequently updated and visually complex part of the UI. Changes must be tested for performance regressions.
- This component is designed to be a highly optimized, special-purpose "leaf" node in the Compose UI tree.
