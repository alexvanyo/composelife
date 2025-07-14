# Module: clock

This module provides an injectable `Clock` instance for the application.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It abstracts the system clock behind an interface, allowing for dependency injection.
- The primary purpose is to enable deterministic testing of time-dependent logic by allowing the real `Clock` to be replaced with a test `Clock` in tests.
- It uses the `kotlinx-datetime` library for time-related operations.

## Usage

- Any component that needs to access the current time should inject the `Clock` from this module rather than using `System.currentTimeMillis()` or other system-level time functions directly.
- In tests, a test double (e.g., a fake or mock `Clock`) can be provided to control the passage of time.

## Key Dependencies

- `kotlinx-datetime`: The underlying library for date and time operations.
- `:inject-scopes`: For dependency injection scopes.

See the [README.md](README.md) for more information.
