# Module: wear-watchface-wff

This module defines the Game of Life watch face using the declarative Watch Face Format (WFF).

## Purpose & Architecture

- This is an Android library module.
- It contains the XML resources that define the layout, components, and behavior of the watch face in the WFF format.
- This approach can offer performance benefits and is an alternative to a fully code-based implementation using `WatchFaceService` and Canvas.
- It may be an experimental alternative or a complement to the `:wear-watchface` module.

## Usage

- The XML files in this module are compiled by the build tools into a functional watch face.
- See the official Android documentation for more information on the Watch Face Format.
