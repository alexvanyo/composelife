# Module: logging

This is a Kotlin Multiplatform library module that provides a standardized logging framework for the application.

## Purpose & Architecture

- This module wraps the **Kermit** logging library.
- It provides a common `Logger` interface that can be injected throughout the application.
- It configures Kermit with platform-specific log writers (e.g., `LogcatLogWriter` for Android).
- This approach centralizes logging configuration and allows for easy swapping of the logging implementation if needed.

## Usage

- Do not use `android.util.Log` or `println` for logging.
- Instead, inject the `Logger` interface provided by this module and use it for all logging.
- This ensures that logs are consistently formatted and can be controlled via the central configuration in this module (e.g., setting log levels for release builds).
