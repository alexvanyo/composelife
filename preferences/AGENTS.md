# Module: preferences

This module is a Kotlin Multiplatform library that provides a type-safe API for storing and retrieving user preferences.

## Purpose & Architecture

- This module uses **Jetpack Proto DataStore** to persist key-value data.
- It uses an Okio-based storage implementation (`androidx.dataStore.core.okio`) to work on all supported platforms (Android, Desktop, etc.).
- The protocol buffer schemas for the preferences are likely defined in the `:preferences-proto` module.
- This module abstracts the DataStore implementation and exposes a simpler, type-safe API (like `PreferencesState`) for other modules to use.

## Source Code Structure

- **`commonMain`**: Contains the primary interfaces and logic for interacting with preferences.
- **`jbMain`**: Contains the common implementation using Jetpack DataStore and Okio.
- Platform-specific source sets (`androidMain`, `desktopMain`) provide any necessary platform-specific wiring.

## Key Considerations

- When adding a new preference, you will likely need to:
    1.  Update the protocol buffer definition in the `:preferences-proto` module.
    2.  Rebuild the project to generate the new proto classes.
    3.  Expose the new preference through the API in this module.
- This module provides data as a `Flow`, allowing other parts of the app to reactively observe preference changes.
