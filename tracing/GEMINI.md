# Module: tracing

This module provides an injectable `TraceDriver` instance for the application.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It provides an injectable `TraceDriver` from the `androidx.tracing` library, allowing for in-process tracing.
- The module targets Android, Desktop (JVM), and WasmJs platforms.
- Appropriate implementations from `tracing-wire` are injected on each platform.

## Usage

- Any component that needs to perform tracing should inject the `TraceDriver` object from this module.

## Key Dependencies

- `androidx.tracing`: The core tracing library.
- `androidx.tracing-wire`: The library providing the Perfetto trace packet format implementations.
- `:inject-scopes`: For dependency injection scopes.
