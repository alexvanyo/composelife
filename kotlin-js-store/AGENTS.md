# Directory: kotlin-js-store

This directory is related specifically to the Kotlin/WasmJS target of the project.

## Purpose & Architecture

- This directory contains a `wasm` subdirectory, which in turn holds a `yarn.lock` file.
- This is used to pin JavaScript dependencies via `yarn` strictly for the WasmJS target, ensuring reproducible JS dependency resolution.
