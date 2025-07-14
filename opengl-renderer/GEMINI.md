# Module: opengl-renderer

This is an Android library module that provides a custom, low-level renderer using OpenGL.

## Purpose & Architecture

- This module contains the implementation for rendering parts of the UI using OpenGL ES.
- It is likely used for performance-critical rendering, such as the cell grid in the `:ui-cells` module, bypassing some of the higher-level abstractions of Jetpack Compose for direct control over the GPU.
- It may contain `GLSurfaceView` implementations, custom shaders (GLSL), and the associated Kotlin code to manage EGL contexts, textures, and drawing commands.

## Usage

- This module is a highly specialized component. It is likely used by only a few specific `@Composable` functions that need maximum rendering performance.
- When working on the cell visualization, be aware that the rendering may be happening in this module rather than in standard Compose `draw` modifiers.
