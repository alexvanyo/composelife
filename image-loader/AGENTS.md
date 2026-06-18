# Module: image-loader

This is a Kotlin Multiplatform library module that provides a platform-agnostic abstraction for loading images.

## Purpose & Architecture

- This module uses the **Coil** library to provide a consistent API for loading images across all supported
  platforms.
- It provides a pre-configured `ImageLoader` object that should be used for all image loading operations.
- This approach avoids the need to write platform-specific code for loading images from different sources.

## Usage

- When you need to load an image, inject and use the `ImageLoader` object provided by this module.
