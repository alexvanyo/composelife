# Module: database

This module is a Kotlin Multiplatform library responsible for the local database implementation.

## Purpose & Architecture

- This module uses **SQLDelight** to create and manage a local SQL database.
- It defines the database schema in `.sq` files and generates type-safe Kotlin APIs for querying the database.
- It provides platform-specific SQLDelight drivers for Android, Desktop (JVM), and WebAssembly (WasmJs).
- The generated database interface is `ComposeLifeDatabase`. SQLDelight is configured to generate `suspend` functions for queries.

## Source Code Structure

- **Schema:** The database schema is defined in `.sq` files located under `src/commonMain/sqldelight/`.
- **Generated Code:** SQLDelight generates Kotlin code based on the schema. This generated code should not be edited manually.
- **`commonMain`**: Contains the `.sq` schema files and any common database-related logic.
- **Platform-specific source sets (`androidMain`, `desktopMain`, `wasmJsMain`)**: These contain the platform-specific driver implementations for SQLDelight.

## Key Considerations

- When modifying the database, you should edit the `.sq` files. The Kotlin database API will be regenerated automatically during the build process.
- For significant schema changes, you will need to write a migration file (`.sqm`).
- This module exposes the raw database access. The `:data` module is responsible for abstracting this into a higher-level repository pattern.
