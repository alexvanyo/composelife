# Module: desktop-app

This module is the primary entry point for the **Desktop (JVM) application**.

## Purpose & Architecture

- This module assembles the shared library modules (like `algorithm`, `data`, `ui-mobile`, etc.) into a runnable JVM desktop application.
- It uses **Jetpack Compose for Desktop** to render the UI.
- The main entry point for the application (`main` function) is located in the `desktopMain` source set.
- This module is responsible for window management and other desktop-specific integrations.
