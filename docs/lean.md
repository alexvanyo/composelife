# Lean 4 Formal Verification Architecture

ComposeLife uses [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4) to formally specify, model, and verify core state machines, cellular automata algorithms, and continuous geometry routines. Verified Lean code is compiled directly to multiplatform Kotlin source code using Lean's Kotlin backend (`lean -K`), running across Android, Desktop JVM, and WebAssembly (Wasm).

This document normatively defines the formalization rules, 4-role architecture, type disciplines, and build system integration required for all Lean components in the repository.

---

## Formalization Policy & Rules

All code and verification in Lean must adhere to four strict rules, enforced by automated checks in the build system:

| Rule | Name | Description | Enforcement |
|:---:|---|---|---|
| **R1** | **Complete Proof Coverage** | Every executable Lean definition compiled to Kotlin must be covered by Lean theorems/proofs, either directly or by a proven equivalence or refinement to a verified mathematical model. | Master theorems in `<Component>Theorems.lean` specify all exported functions. Lake verification checks all proofs. |
| **R2** | **No Verbatim Kotlin in Build Scripts** | Verbatim Kotlin code must be kept to a minimum and must live exclusively in Kotlin source files (`src/commonMain/kotlin`) or Lean files (`FileSpec` / `kotlin_member`). **Never in Gradle build scripts (`*.gradle.kts`)**. | Automated build script hygiene check fails if any `*.gradle.kts` contains inline Kotlin blocks (`footerFile`, `preambleFile`, or Kotlin code strings). |
| **R3** | **Fixed-Width Production Types** | Production (compiled) Lean code must use fixed-width programming types (`UInt8/16/32/64`, `Int8/16/32/64`, `Float`, `Bool`), never unbounded types (`Nat`, `Int`, `ℚ`) that emit `BigInteger`. Unbounded and continuous types are restricted to non-compiled specifications, models, and proofs. | `checkLeanGeneratedKotlin` fails if generated Kotlin code contains `BigInteger`, `Nat`, or `java.math`. |
| **R4** | **Warnings as Errors** | All Lean builds and code generation invocations must treat warnings as fatal errors. | Lake verification runs with `--wfail`; Lean compiler runs with `-DwarningAsError=true`. |

---

## The 4-Role Architecture

To keep production code clean, maintain fast compilation, and clearly distinguish between formal specifications, master guarantees, and tactical proofs, every Lean component is structured into four distinct roles:

```
┌────────────────────────────────────────────────────────┐
│  1. Production Executable Code                         │
│     (<Component>.lean, <Component>/*.lean)             │
│     - Pure executable definitions and algorithms       │
│     - Fixed-width types only (UInt32/64, Int32, Float) │
│     - 0 theorems, 0 proofs, 0 heavy tactic imports     │
│     - Compiled directly to Kotlin via `lean -K`        │
└────────────────────────────────────────────────────────┘
                           ▲
                           │ specifies behavior / proven equivalent
┌──────────────────────────┴─────────────────────────────┐
│  2. Specification Definitions                          │
│     (<Component>Defs.lean)                             │
│     - Mathematical definitions, models & predicates    │
│     - Unbounded / continuous types (Nat, Int, ℚ, ℝ)    │
│     - 0 proofs                                         │
└──────────────────────────┬─────────────────────────────┘
                           │ used in signatures
┌──────────────────────────┴─────────────────────────────┐
│  3. Master Theorems                                    │
│     (<Component>Theorems.lean or theorems/*.lean)      │
│     - High-level public contract & correctness claims  │
│     - 0 proof bodies (zero `by` tactics)               │
│     - Every theorem delegates directly to `_Impl`:     │
│       theorem my_claim : Prop := my_claim_Impl         │
└──────────────────────────▲─────────────────────────────┘
                           │ delegates proof to
┌──────────────────────────┴─────────────────────────────┐
│  4. Implementation Proofs                              │
│     (<Component>Proofs.lean or proofs/*.lean)          │
│     - Tactical proofs, intermediate lemmas, arithmetic │
│     - Defines the `..._Impl` theorems                  │
│     - Imports Mathlib, tactical solvers (omega, etc.)  │
└────────────────────────────────────────────────────────┘
```

### 1. Production Executable Code (`<Component>.lean`, `<Component>/*.lean`)
- **Purpose**: Defines executable functions and state machines compiled to Kotlin.
- **Rules**:
  - Must contain **executable code only**.
  - Must use **fixed-width types** only (`UInt8/16/32/64`, `Int8/16/32/64`, `Float`, `Bool`).
  - Must contain **no proofs or non-equational theorems**.
  - Must **not** import proof-only modules (such as `Mathlib.Tactic.*` or analysis libraries).
  - Must export clean entrypoints with `@[export]` or `kotlin_member`.

### 2. Specification Definitions (`<Component>Defs.lean`)
- **Purpose**: Defines the mathematical ideal, continuous geometry, game-of-life grid transitions, or transition invariants against which production code is evaluated.
- **Rules**:
  - Contains definitions (`def`, `inductive`, `structure`, `class`) and predicates (`Prop`), but **no proofs**.
  - May freely use unbounded types (`Nat`, `Int`, `ℚ`, `ℝ`).
  - Is **never** compiled to Kotlin; exists solely to define correctness.

### 3. Master Theorems (`<Component>Theorems.lean` or `theorems/*.lean`)
- **Purpose**: The public, human-readable specification contract. Reviewers can read these files to audit the exact mathematical guarantees without sifting through proof tactics.
- **Rules**:
  - Contains **only meaningful specification theorems** covering compiled definitions.
  - Contains **zero proof bodies** (no `by`, `sorry`, or inline tactics).
  - Every master theorem delegates directly to its `_Impl` counterpart:
    ```lean
    theorem computeNextGen4x4_correct (w : UInt32) (h : w < 65536) :
        decode4x4Center (computeNextGen4x4 w) = naiveCenter2x2 (decode4x4 w) :=
      computeNextGen4x4_correct_Impl w h
    ```

### 4. Implementation Proofs (`<Component>Proofs.lean` or `proofs/*.lean`)
- **Purpose**: Tactical proofs, intermediate lemmas, induction arguments, and solver invocations (`omega`, `linarith`, `ring`, `bv_decide`).
- **Rules**:
  - Implements the `..._Impl` theorems referenced in master theorems.
  - May import full Mathlib and tactical solvers.

---

## Specification vs. Production Types

| Concept | Production (Compiled) | Specification / Model (Non-compiled) |
|---|---|---|
| Integers | `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Int8`, `Int16`, `Int32`, `Int64` | `Nat` ($\mathbb{N}$), `Int` ($\mathbb{Z}$) |
| Reals / Fractions | `Float` (IEEE 754 float/double) | `Rat` ($\mathbb{Q}$), `Real` ($\mathbb{R}$) |
| Collections | Fixed arrays, bitboards, primitive words | Lists, infinite grids `(ℤ × ℤ) → Bool`, Mathlib sets |
| Generated Kotlin | Kotlin primitives: `Int`, `Long`, `UInt`, `ULong`, `Double`, `Float`, `Boolean` | Forbidden: emits `BigInteger` / `Nat` (fails build) |

---

## Proof Obligation Patterns

Depending on the domain, master theorems cover compiled definitions via one of two patterns:

### Pattern A: Direct Equivalence
Used when the compiled definition directly computes the discrete state update (e.g. cellular automata bitboards):
```lean
theorem computeNextGen4x4_correct (w : UInt32) (h : w < 65536) :
    decode4x4Center (computeNextGen4x4 w) = naiveCenter2x2 (decode4x4 w) :=
  computeNextGen4x4_correct_Impl w h
```

### Pattern B: Continuous Model Refinement Under Preconditions
Used when continuous or floating-point operations refine a real/rational model (e.g. geometry ray-marching):
```lean
theorem rayMarchSegmentCoords_refines
    (sx sy ex ey : Float) (cx cy ex' ey' : Int32)
    (hPre : InRange sx sy ex ey cx cy ex' ey') :
    toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey') =
      cellIntersectionsSegmentFloat (toPoint32 sx sy) (toPoint32 ex ey) :=
  rayMarchSegmentCoords_refines_Impl sx sy ex ey cx cy ex' ey' hPre
```
The precondition (`InRange`) explicitly documents the domain constraints (such as coordinates strictly within $[-2^{30}, 2^{30}]$ to guarantee no integer overflow).

---

## Kotlin Integration & Code Boundaries

1. **Lean-to-Kotlin Compilation**:
   The custom Lean 4 compiler generates Kotlin source code directly:
   ```bash
   lean -DwarningAsError=true \
        -Dcompiler.kotlin.pruneUnreachable=true \
        -Dcompiler.kotlin.package=com.alexvanyo.composelife.algorithm \
        -K build/generated/sources/lean/kotlin/commonMain/.../HashLifeLean.kt \
        Algorithm/HashLife.lean
   ```
2. **Minimal Verbatim Code**:
   - Signature mapping, file layout, and package annotations are declared in Lean using `@[kotlin_file]` and `kotlin_member`.
   - High-level idiomatic Kotlin APIs (such as Compose `Offset` extensions or `MacroCell` convenience wrappers) reside in `src/commonMain/kotlin/`.
   - **Zero verbatim Kotlin is permitted in Gradle build scripts**.

---

## Standardized Build Logic (`convention-lean`)

The Gradle convention plugin `com.alexvanyo.composelife.lean` (configured in `build-logic`) standardizes all Lean operations across modules:

### Configured Tasks
- `cacheLean`: Runs `lake exe cache get` with task concurrency limits.
- `verifyLean`: Runs `lake build --wfail <Target>:static`, failing on any warning. Automatically hooked into `./gradlew check`.
- `generateLeanKotlin`: Runs `lean` with `-DwarningAsError=true` and `-K`, outputting Kotlin into Gradle's generated sources directory. Automatically added to `commonMain` source set.
- `checkLeanGeneratedKotlin`: Inspects generated Kotlin to ensure no `BigInteger`, `Nat`, or `java.math` imports are present.
- `checkLeanBuildScriptHygiene`: Asserts no verbatim Kotlin code is embedded in `build.gradle.kts`.

### Verification Commands
```bash
# Verify Lean formalization across modules
./gradlew :session-value:verifyLean
./gradlew :geometry:verifyLean
./gradlew :algorithm:verifyLean

# Full check including proof verification, codegen checks, and test suites
./gradlew check
```

---

## Axiom Auditing

Every master theorem must depend only on standard Lean foundational axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`

Master theorems must never depend on `sorry` or custom unverified axioms. Verify axiom dependencies in Lean via:
```lean
#print axioms computeNextGen4x4_correct
```
