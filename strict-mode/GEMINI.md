# Module: strict-mode

This module provides a way to configure and enable Android's `StrictMode`.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module, but its functionality is specific to Android.
- It provides a centralized mechanism for enabling and configuring `StrictMode`, a developer tool that detects things you might be doing by accident and brings them to your attention so you can fix them. For example, it can be configured to detect accidental disk or network access on the main thread.
- This module contains logic to enable `StrictMode` only in debug builds.

## Usage

- This module is typically initialized early in the application's lifecycle to set up the desired `StrictMode` policies.

## Key Dependencies

- `:logging`: To log `StrictMode` violations.
