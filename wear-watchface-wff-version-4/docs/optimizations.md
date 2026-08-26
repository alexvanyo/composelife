# Watch Face Format (WFF) Size Optimizations

This document details the size optimization techniques implemented to reduce the Watch Face Format (WFF) APK and uncompressed resource footprint in `wear-watchface-wff-version-4` while maintaining complete visual and functional fidelity.

---

## Summary of Results

| Optimization Technique | Target Area | Uncompressed Reduction | APK Reduction | Status / Commit |
|---|---|---|---|---|
| **1. TTF Font Generation Flags** | Font TTFs (`post` & instructions) | ~11.29 MB across all 33 fonts (~342 KB/font) | ~3.20 MB | `5e90d2300` |
| **2. Unused Resource Removal** | Raw resources (`watchface_testing.xml`) | 342,737 bytes (342.7 KB) | ~13 KB | `f3aac3e84` |
| **3. Glyph Outline Deduplication (`AltUni2`)** | Glyph outlines (`glyf` & `cmap` tables) | 151,974,816 bytes (144.93 MB, 38.2%) | ~1.24 MB | `a7368749a` |
| **4. XML Whitespace & Indentation Minification** | `watchface.xml` raw resource | 700,695 bytes (700.7 KB, 11.0%) | ~24 KB | `4299a8f21` |
| **Total Cumulative Savings** | **Entire Watch Face** | **~164.3 MB Uncompressed** | **~4.5 MB Compressed APK** | **All Verified** |

---

## Detailed Technique Breakdown

### 1. TTF Font Generation Flags (`short-post` & `no-hints`)
- **Commit:** `5e90d2300`
- **Affected Files:** `wear-watchface-wff-resources/build.gradle.kts`
- **Description:**
  When generating the 33 hour TrueType fonts (`hour00.ttf` through `hour23.ttf` and 12-hour specific variants), FontForge was previously invoked with default flags, generating a Format 2.0 `post` table containing full string names for all 18,000 glyphs in each font file, as well as TrueType hinting tables (`fpgm`, `prep`, `cvt`).
- **Implementation:**
  Updated the FontForge `Generate(...)` call in `ConvertSfdToTtf` task to pass flag value `12`:
  - Bit `4` (`short-post`): Generates a Format 3.0 `post` table, omitting glyph name strings and referencing glyphs purely by index.
  - Bit `8` (`no-hints`): Disables instruction and hint generation, which are unnecessary for 70x70 pixel grid cells.
- **Impact:**
  - **Uncompressed Font Reduction:** ~342 KB per font TTF (~11.29 MB total across 33 fonts)
  - **APK Size Reduction:** ~3.20 MB

---

### 2. Unused Resource Removal (`watchface_testing.xml`)
- **Commit:** `f3aac3e84`
- **Affected Files:** `wear-watchface-wff-version-4/src/main/res/raw/watchface_testing.xml` (Deleted)
- **Description:**
  An orphaned 342 KB test XML file (`watchface_testing.xml`) was present in `wear-watchface-wff-version-4/src/main/res/raw/`. Because resource shrinking is disabled for WFF modules (`isShrinkResources = false`), this unused file was packaged into every release and debug build artifact.
- **Implementation:**
  Deleted the unreferenced test XML file from the module source set.
- **Impact:**
  - **Uncompressed Resource Reduction:** 342,737 bytes (342.7 KB)
  - **APK Size Reduction:** ~13 KB

---

### 3. Glyph Outline Deduplication via `AltUni2` `cmap` Mapping
- **Commit:** `a7368749a`
- **Affected Files:**
  - `wear-watchface-wff-resources/src/jvmTest/kotlin/com/alexvanyo/composelife/wear/watchface/DestructionTests.kt`
  - `wear-watchface-wff-resources/build.gradle.kts`
- **Description:**
  Each hour font encompasses 60 minutes with 300 generations per minute (18,000 total glyphs per font). In Conway's Game of Life, destruction patterns stabilize into still lifes (period 1) or periodic oscillators (periods 2, 3, etc.) after approximately 100–150 generations. For the remainder of the 300 generations, the cell state repeats identical patterns.
  Previously, full contour outline data was emitted for every single generation (18,000 separate `glyf` entries per font), duplicating over 5,788 glyphs (32.2%) per font file.
- **Implementation:**
  - In `DestructionTests.kt`, grouped identical cell states within each minute during SFD generation.
  - For repeating states, emitted the contour outline once under the canonical generation index and mapped subsequent matching generations using FontForge's `AltUni2: <hex_codepoint>.ffffffff.0` directive.
  - FontForge compiles `AltUni2` by creating a single glyph entry in the TrueType `glyf` table while mapping multiple Unicode codepoints to that shared glyph ID in the TrueType `cmap` subtable.
- **Impact:**
  - **Uncompressed Font Reduction:** 151,974,816 bytes (144.93 MB, 38.2% reduction across 33 fonts, dropping total TTF size from 379.34 MB down to 234.40 MB)
  - **APK Size Reduction:** ~1.24 MB

---

### 4. XML Whitespace and Indentation Minification
- **Commit:** `4299a8f21`
- **Affected Files:** `wear-watchface-wff-version-4/src/main/res/raw/watchface.xml`
- **Description:**
  The `watchface.xml` file spans over 13,000 lines and defines 33 distinct hour font branches, each containing an 18,000-character XML entity string (`&#x4e00;&#x4e01;...`). Deep nesting contributed significant whitespace indentation across tags and attributes.
- **Implementation:**
  Minified leading and trailing line whitespace throughout `watchface.xml` while preserving all element structures, CDATA blocks, expression contents, attribute formatting, and numeric character entities.
- **Impact:**
  - **Uncompressed Resource Reduction:** 700,695 bytes (700.7 KB, 11.0% reduction in `watchface.xml`)
  - **APK Size Reduction:** ~24 KB

---

## Verification & Compatibility

All optimizations were verified through:
1. **Automated CI Validation:** Successful run of `./gradlew check` (including detekt, unit tests, integration tests, Android lint, and resource checks).
2. **Dual-Emulator Visual Verification:** Deployed side-by-side to two Wear OS emulators (`emulator-5554` baseline and `emulator-5556` target) comparing interactive animations and ambient display modes via screenshot capture.
