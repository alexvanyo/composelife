# Module: resources-app

This module provides Android resources specifically for the main application targets (`:app`).

## Purpose & Architecture

- This is a Kotlin Multiplatform library module that contains Android resources.
- It depends on the `:resources-common` module, which contains resources shared across all form factors.

## Usage

- The `:app` module depends on this module to access these resources.

## Key Dependencies

- `:resources-common`: For the base set of shared resources.
