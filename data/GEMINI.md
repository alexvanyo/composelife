# Module: data

This module acts as the data layer for the application, following the repository pattern.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It is responsible for abstracting the origin of data (e.g., from the network, a local database, or in-memory cache) from the rest of the application.
- It defines repository interfaces and their implementations, which are the primary way for UI and feature modules to interact with application data.
- It depends on lower-level modules like `:database` and `:preferences` to fetch and store data.

## Source Code Structure

- **`commonMain`**: Contains the platform-agnostic repository interfaces and data models.
- **`jbMain`**: Contains the primary implementations of the repositories.
- Platform-specific implementations or dependencies are placed in the corresponding source sets (`androidMain`, etc.).
