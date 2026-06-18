# Module: resources-wear

This module provides resources specifically for the Wear OS application.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module that contains Android resources tailored for Wear OS.
- It depends on the `:resources-common` module for assets that are shared across all platforms.
- This module is intended to hold resources that are specific to the watch form factor, such as strings, drawables, styles, or other assets that are optimized for a small, round or square screen.

## Usage

- The `:wear` module and other Wear-specific UI modules (like `:ui-wear`) depend on this module to access these resources.
- Place resources here if they are only used on Wear OS.

## Key Dependencies

- `:resources-common`: For the base set of shared resources.
