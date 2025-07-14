# Module: strict-mode

This module is responsible for configuring and enabling Android's `StrictMode`.

## Purpose & Architecture

- This is an Android-only library module.
- `StrictMode` is a developer tool that detects things you might be doing by accident and brings them to your attention so you can fix them. For example, it can detect accidental disk or network access on the main thread.
- This module likely contains code to initialize `StrictMode` with a specific policy during application startup, probably only in debug builds.

## Usage

- This module is typically included in the main `:app` module to enable `StrictMode` during development.