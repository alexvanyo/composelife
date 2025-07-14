# Module: app-compat-sync

This module is responsible for synchronizing user preferences with Android's `AppCompat` framework.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module, primarily targeting Android.
- It listens for changes in user preferences (from the `:preferences` module) and applies them to `AppCompat` components.
- A key example of its function is updating the application's theme (e.g., Day/Night mode) via `AppCompatDelegate` based on the user's selection in the settings.
- This ensures that legacy `AppCompat` components and the overall application theme are consistent with the user's choices, which are managed in a platform-agnostic way.

## Key Dependencies

- `:preferences`: To observe and retrieve user preference data.
- `androidx.appcompat`: To interact with the `AppCompat` framework.
- `:inject-scopes`: For dependency injection scopes.
- `:updatable`: To handle updatable values.

See the [README.md](README.md) for more information.
