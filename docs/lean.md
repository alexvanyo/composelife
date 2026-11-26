# Lean 4 Formal Verification Architecture

ComposeLife uses [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4) in two complementary ways:

1. **Lean-first code generation (`lean -K`)**: Core state machines, cellular automata algorithms, and continuous geometry routines are written in Lean, formally proved against mathematical specifications, and compiled directly to multiplatform Kotlin running across Android, Desktop JVM, and WebAssembly (Wasm).
2. **JVM bytecode verification (`jvm-lean`)**: Compiled JVM `.class` bytecode—both from Lean-generated Kotlin (`JvmBytecode.lean`) and from **existing hand-written Kotlin** (`KotlinJvmBytecode.lean`)—is lifted into Lean and proved equivalent to Lean models and domain theorems under a shared operational JVM semantics, with standard Kotlin `@Test` suites checking the live test-classpath bytecode.

This document normatively defines the formalization rules, when and how to choose each approach, the 4-role architecture, shared JVM bytecode semantics, type disciplines, and build system integration required for all Lean components in the repository.

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

## Choosing an Approach: Lean-First Codegen vs. Proving Existing Kotlin

Use the table below to decide whether a component should be written in Lean and compiled to Kotlin, or kept in hand-written Kotlin and verified via JVM bytecode lifting:

| Criterion | Write in Lean & Generate Kotlin (`lean -K`) | Keep Hand-Written Kotlin & Prove JVM Bytecode (`jvm-lean`) |
|---|---|---|
| **Best fit** | New or core pure algorithms, parsers, lookup tables, recursive trees/bitboards, and finite state machines (`HashLife`, `MacroCell`, `FlatHashLife`, `RLE`/`Life105`/`Life106`/`Plaintext`, `RayMarch`, `SessionValue`). | Existing idiomatic Kotlin functions using `inline value` classes, Compose geometry types (`Offset`, `IntOffset`), `@Composable` wrappers, Kotlin collections/`Set`/`List`, `<clinit>` tables, or Kotlin-specific stdlib calls (`BitComputationKt`, `HashLifeComputationKt`, `MacroCellCoordinatesKt`, `GameOfLifeStepKt`, `CellWindow`, `DeserializationResultKt`, `CellState`, `Cache`/`Equivalence`, `GeometryExtensionsKt`, `OffsetExtensionsKt`, `RectExtensionsKt`, `IntSizeLerpKt`, `LineSegmentKt`/`LineSegmentPath`, `BackstackNavigationKt`, `BackstackEntry`/`BackstackStateKt`, `ResourceStateKt`, `PeriodUntilKt`, `TargetStateKt`, `EasingPiecewiseKt`, `ColorComponentKt`, `WindowInsetsLerpKt`/`PaddingValuesExtensionsKt`/`NonNegativeLong`/`NonNegativeDouble`, `GridDraggableAnchors2d`/`MutableCellWindowViewportStateImpl`, `serialization` serializers, `mosaic-calculator`). |
| **Multiplatform artifact** | Emits `commonMain` Kotlin automatically for Android, Desktop JVM, and Wasm from one verified source. | Production Kotlin remains untouched in `commonMain`/`jvmMain`; verification applies directly to the compiled JVM `.class` bytecode. |
| **What is verified** | Master theorems prove properties of the Lean source definitions; `JvmEquiv` separately proves the JVM bytecode emitted by `kotlinc` matches those Lean definitions. | A standalone Lean model + domain theorems are proved in Lean (never using codegen as the source of truth), and a JVM equivalence proof links the real `.class` bytecode to that model. |
| **Compiler assumptions** | Trusts the custom Lean-to-Kotlin compiler (`av/jvm`) and any `kotlin_expr`/`FileSpec` shims to match Lean execution semantics. | Trusts `jvm-lean`'s operational model of JVM bytecode instructions and module hooks (`<clinit>`, Kotlin stdlib/Compose inline helpers) to match the JVM runtime. |
| **Gradle / Test integration** | `verifyLean`, `generateLeanKotlin`, `checkLeanGeneratedKotlin`, and `verifyLeanJvmBytecode` (for `JvmBytecode.lean`). | `verifyLeanJvmBytecode` (`kotlinBytecodeClassPaths` -> `KotlinJvmBytecode.lean` + `#audit_jvm_equiv_axioms`) plus optional Kotlin `@Test` suites via `:lean-test-fixtures`. |

Rule of thumb:
- **Prefer Lean-first codegen** when designing self-contained computational kernels or state machines whose API can be exposed cleanly with `@[export]` / `kotlin_member`.
- **Prefer JVM bytecode verification** when the code is already written in idiomatic Kotlin, relies on Kotlin/Compose value classes or standard collections (`List`/`Set`/`Iterator`), or when you want to verify existing Kotlin without rewriting it into Lean.
- **Note on trust boundaries**: Lean-first components covered by `verifyLeanJvmBytecode` also gain end-to-end JVM assurance—their source Lean proofs connect through `JvmEquiv` proofs all the way down to the compiled `.class` instructions produced by `kotlinc`.

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
  - Must contain **no proofs or non-equational theorems**. The one exception is a termination lemma that a
    fuel-indexed loop's `decreasing_by` needs (such as `uint32_sub_one_lt` in `Algorithm/MacroCell.lean`).
  - Must **not** import proof-only modules (such as `Mathlib.Tactic.*` or analysis libraries).
  - Non-compiled specification models (such as `FloatModel.lean` or `Basic.lean`) must reside outside `<Component>/` in a dedicated directory (e.g. `models/`), ensuring only production code is compiled to Kotlin.
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
  - Contains **zero proof bodies** (no `by`, `sorry`, `rfl`, anonymous constructors or inline tactics), including
    for concrete checks such as `deserializeRLE #[] = ⟨.emptyFile, #[.emptyFile], #[]⟩`.
  - Every master theorem delegates directly to its `_Impl` counterpart:
    ```lean
    theorem computeNextGen4x4_correct (w : UInt32) (h : w < 65536) :
        decode4x4Center (computeNextGen4x4 w) = naiveCenter2x2 (decode4x4 w) :=
      computeNextGen4x4_correct_Impl w h
    ```
- **Naming** (`X` / `X_Impl`):
  - A master theorem `X` has a plain, descriptive name: what it states (`deserializeRLE_eq_rleSpec`,
    `rle_round_trip_box`, `flat_internLevel4_correct`). It never ends in `_Impl`, `_spec` or `_thm`. When the
    obvious name is taken by a definition (`deserializeRLE`), name the statement (`deserializeRLE_eq_rleSpec`)
    rather than adding a suffix.
  - Its proof is exactly `X_Impl`, in an implementation proof module, with the same statement and parameters. The
    body of `X` is `X_Impl` applied to the explicit parameters of `X`, in order, and nothing else.
  - Every `_Impl` theorem is the proof of exactly one master theorem: no master theorem without an `_Impl`, and
    no `_Impl` without a master theorem.
  - Each package's `AxiomAudit.lean` enforces these rules with `#audit_master_theorem_names`, which fails the build
    on a master theorem with a `_Impl`, `_spec` or `_thm` suffix, a master theorem that is not `X_Impl` applied to
    its parameters, or an `_Impl` theorem in a proof module with no master theorem.

### 4. Implementation Proofs (`<Component>Proofs.lean` or `proofs/*.lean`)
- **Purpose**: Tactical proofs, intermediate lemmas, induction arguments, and solver invocations (`omega`, `linarith`, `ring`, `decide`, `bv_check`).
  - Implements the `..._Impl` theorems referenced in master theorems.
  - **Naming**:
    - `X_Impl` is reserved for the proof of the master theorem `X` (see [Master Theorems](#3-master-theorems-componenttheoremslean-or-theoremslean)).
      Other proofs use it like any lemma, but nothing else is named `_Impl`.
    - When a master theorem is a lemma that the proofs also use widely (for example `WFd_level_toNat`, or
      `parseInt32At_spec`), keep the lemma's name and add a one-line `X_Impl` beside it that restates `X` and
      applies the lemma, rather than renaming the lemma after `X`.
    - When `X` combines several lemmas (`⟨h.1, l.1, h.2, l.2⟩`, `(lemma ...).2 h`), that term is the body of
      `X_Impl`, not of `X`.
    - Concrete checks (`decide +kernel`, `rfl`) are `X_Impl` theorems too, conventionally grouped under a
      `Concrete checks of the master theorems` heading at the end of a proof module.
    - Internal lemmas are named for what they state. `f_spec` is a lemma stating what the definition `f`
      computes (`scanDigits_spec`, `expandRuns_spec`); a specification *definition* is named `fooSpec`
      (`rleSpec`, `linesSpec`) and lives with the proofs or in `<Component>Defs.lean`.
  - May freely use heavy tactical solvers (`omega`, `linarith`, `ring`, `aesop`, `positivity`). See the [Proof Tactics Guide](#proof-tactics-guide).
  - May import full Mathlib and tactical solvers.
  - May be decomposed across multiple submodules and directories when proofs grow large.
  - **Hierarchy Rule**:
    - **Single Domain / Component**: Placed in `<Component>Proofs.lean` (e.g., `SessionValueProofs.lean`).
    - **Multiple Modules**: Placed in a `proofs/` subfolder (e.g., `algorithm/lean/proofs/` or `geometry/lean/proofs/`), re-exported by `<Component>Proofs.lean`.

### Mutation Proofs (`proofs/Mutations.lean`)
Each package also has a `proofs/Mutations.lean`, evidence that its master theorems are strong:
- **Mutants**: a plausible buggy variant of a compiled function (a kernel reading a shifted word, a lookup table
  one bit too small, a ray march that skips cells), with a proof that it violates the property a master theorem
  proves for the real function. A master theorem that a mutant also satisfies is too weak.
- **Non-vacuity**: a proof that the hypotheses of the conditional master theorems hold together for real inputs
  (for example `InRange` for a concrete `cellIntersections` call, or `ArenaWF` with the capacity bounds for an
  arena as `createFlatArena` builds it). A theorem whose hypotheses never hold proves nothing.

Prove concrete cases with `decide +kernel`, which evaluates in the kernel and adds no axioms. Mutation modules are
roots of the dead-proof search and are covered by the axiom audit.

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

### Pattern B: Floating-Point Refinement Under Preconditions
Used when compiled floating-point code refines a float model whose own properties are proven separately against an exact rational or real model (e.g. geometry ray-marching):
```lean
theorem rayMarchSegmentCoords_refines (A B : Point32) (sx sy ex ey : Float) (cx cy ex' ey' : Int32)
    (hPre : InRange A B sx sy ex ey cx cy ex' ey') :
    dedupCells (toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey')) =
      cellIntersectionsSegmentFloat A B :=
  rayMarchSegmentCoords_refines_Impl A B sx sy ex ey cx cy ex' ey' hPre
```
The precondition (`InRange`) states only the domain of the compiled function, never its behavior:
1. The model endpoints are finite and within a coordinate bound under which no `Int32` or `Float` intermediate overflows.
2. The `Float` arguments are the values the Kotlin caller passes (here, the exact widenings of `Float32` coordinates).
3. The `Int32` cell arguments are the floored endpoint cells.

A precondition must **never** restate the conclusion, or any equation about the compiled function's output, under any name. If a property of the compiled code cannot be proven, the theorem is not a refinement theorem. Before adding such a hypothesis, check that it is satisfiable on real inputs: a hypothesis that is false for every interesting input makes the theorem vacuous.

The output is deduplicated (`dedupCells`) because the compiled march may report a cell twice, while the Kotlin caller collects the cells into a `Set`.

#### Native Floating-Point Semantics
In Lean 4.34, native `Float` arithmetic, negation, comparisons and integer conversions have a logical model (`Float.Model`, an IEEE-754 binary64 word unpacked to `Float.Model.UnpackedFloat`); only transcendental functions and `Float32.toFloat` are opaque. Prove compiled floating-point code correct by relating each native operation to an independent library (FloatLib) and transferring that library's lemmas, as Lean's own model documentation recommends:
- FloatLib proves addition and subtraction (`ofFloat_add_of_isFinite`, `ofFloat_sub_of_isFinite`) and the integer conversions.
- `geometry/lean/proofs/NativeFloat.lean` adds multiplication (`ofFloat_mul_of_isFinite`), comparisons (`native_lt_iff`, `native_le_iff`), negation and `Int32.toFloat`, and packages them as `Agree`: a native float and a FloatLib value that are finite and denote the same real number, preserved by every operation the ray march uses.
- `geometry/lean/proofs/CompiledRayMarch.lean` then proves the compiled loop equal to the model loop by induction on its fuel.

These bridges are proofs about Lean's logical model of `Float`. Like every Pattern A or B theorem, they trust the compiler (here, the Kotlin backend's translation of `Float` operations to Kotlin `Double`) to implement that model.

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

3. **Substitutions and Callbacks Need Their Own Theorems**:
   R1 covers what actually runs in Kotlin, which is not always the Lean body of a function:
   - `kotlin_expr` replaces calls to a Lean function with a Kotlin expression. Each substitution needs a theorem
     that the replacement computes the same thing: for example, `computeNextGen4x4UInt_eq_lookup` (the 4x4 lookup
     table), `centeredSubSubnodeFast_eq_centeredSubSubnode`, `emptySubnode_eq_emptyNode_of_WFd`,
     `macroCell_level_eq_depth` and `macroCell_size_eq` (the cached `level()` and `size()` of `MacroCell.kt`).
     Check the generated Kotlin as well: an `@[inline]` function is inlined before `kotlin_expr` applies (as
     `popcount64` is), so its Lean body is what runs.
   - A compiled function that takes callbacks (`stepCellNodeWith`, `canonicalizeMacroCellWith`) is specified for
     every callback that satisfies a contract describing the Kotlin side, such as "a canonical map returns a
     value equal to its key". The contract describes the callback, never the compiled function's output.
   - Hand-written Kotlin loops that drive compiled functions are modeled as reachability relations or iterations
     and proven correct: `FlatRun` (`FlatLeanHashLifeAlgorithm`), `AsyncReachable` (`rememberAsyncSessionValueHolder`),
     `compiledPathCells` (`cellIntersections(points)`), `DagIntern` (the memoized recursion of `internMacroCellDag`,
     which imports each node with `importMacroCellNode`).
   - A lazy Kotlin iterator runs a compiled Lean step function on an explicit stack: the cell cursor
     (`cellCursorStepAll`, `cellCursorStepInWindow`) pops a frame and pushes its pieces, or emits the live cells of
     one leaf as a 64-bit mask. `cellCursorRun` models the Kotlin loop (step until the stack is empty, then emit
     the set bits of each mask in increasing order), and `flat_cellCursorAll_correct`/`_InWindow_correct` prove it
     stops and emits each live cell exactly once. Kotlin calls each step through an `...Into` member, which passes
     the step's result to an inline lambda instead of returning a tuple (`flat_cellCursorStepInto_eq`), as the
     generation loop does with `stepOneGenerationInto` (`flat_stepOneGenerationInto_eq`). These need the Lean fork
     to support type parameters after a member's receiver (`tests/kotlin/generic_members.lean` there).
     `fitsInIntRange` runs the same cursor over the regions past
     `Int.MAX_VALUE` (`flat_fitsInIntRange_correct`), unless the O(1) check of the root's square settles it
     (`flat_rootFitsInIntRange_sound`). The cursor's frames, not a callback, carry its progress, so nothing about
     how often Kotlin calls it is trusted.
   - Kotlin field writes are modeled by Lean functions: `arena.overflow = 0u` is `clearOverflow` (a `FlatRun`
     step), and replacing the scratch tables to make room for a copy is `withScratch`, which keeps every node and
     state (`flat_withScratch_correct`), so the arena can still start a `FlatRun` or receive a compaction.

   What remains trusted: the Lean-to-Kotlin compiler; verbatim Kotlin emitted from Lean (`FileSpec` items such as
   the `MacroCell` class body and the table initializers); Kotlin's own `countOneBits`, `Uuid` equality and
   `Double` arithmetic and the `countTrailingZeroBits`/`mask and (mask - 1)` walk over a mask's set bits; the
   Kotlin memo tables and canonical maps meeting their contracts (including the
   `internMacroCellDag` memo returning, for a node, an id stored for an equal node); and the small Kotlin glue that
   packs cells into keys (`coordKey`) and decodes them (`keyCoord`), proven inverse in Lean.

### Custom Lean Compiler (`av/jvm`)
Code generation requires a custom Lean 4 compiler fork supporting the Kotlin emission backend (`-K`).
- **Repository**: [`https://github.com/alexvanyo/lean4.git`](https://github.com/alexvanyo/lean4.git)
- **Branch**: `av/jvm`
- **Local Setup**:
  To build and install the compiler locally:
  ```bash
  ./script/build-custom-lean.sh
  ```
  This clones the fork, compiles `stage1` with release optimizations, strips debug symbols to minimize disk footprint (~3GB uncompressed), and installs into `~/.lean-custom/bin/lean`.
- **Compiler Resolution Order**:
  The Gradle plugin resolves the Lean compiler binary in the following order:
  1. Gradle property `-PleanBinary=...`
  2. System property `-DleanBinary=...`
  3. Environment variable `export LEAN_BINARY=...`
  4. Standard user install path: `~/.lean-custom/bin/lean`
  5. Local build directory: `~/Projects/lean4/build/release/stage1/bin/lean`
  6. Project directory path: `.lean-custom/bin/lean`
- **CI Caching**:
  In CI workflows, `setup-custom-lean` resolves the remote commit SHA of `alexvanyo/lean4:av/jvm` and caches the stripped distribution with `actions/cache@v6` under `lean-custom-${{ runner.os }}-${{ sha }}`. Parallel matrix jobs restore the cached compiler in ~5 seconds.

---

## Standardized Build Logic (`convention-lean`)

The Gradle convention plugin `com.alexvanyo.composelife.lean` (configured in `build-logic`) standardizes all Lean operations across modules:

### Configured Tasks
- `cacheLean`: Runs `lake exe cache get` with task concurrency limits.
- `verifyLean`: Runs `lake build --wfail <Target>:static`, failing on any warning. Automatically hooked into `./gradlew check`. Its stamp only counts as up to date while Lake's build of the target (`.lake/build`) still exists, so a `lake clean` reruns it.
- `generateLeanKotlin`: Runs `lean` with `-j 2 -M 4096 -DwarningAsError=true` and `-K`, outputting Kotlin into Gradle's generated sources directory. Automatically added to `commonMain` source set.
- `checkLeanGeneratedKotlin`: Inspects generated Kotlin to ensure no `BigInteger`, `Nat`, or `java.math` imports are present.
- `checkLeanBuildScriptHygiene`: Asserts no verbatim Kotlin code is embedded in `build.gradle.kts`.
- `verifyLeanJvmBytecode`: Lifts compiled desktop JVM `.class` outputs from both generated `entries` (`JvmBytecode.lean`) and `kotlinBytecodeClassPaths` (`KotlinJvmBytecode.lean`) via `script/jvm-bytecode2lean.py`, compiles `proofs/JvmEquiv/*.lean` and `proofs/KotlinJvmEquiv/*.lean` submodules in topological order (recompiling the bytecode olean and each submodule only when the lift, a dependency olean, or the source changed), and elaborates `proofs/JvmEquiv.lean` / `proofs/KotlinJvmEquiv.lean` with `-DwarningAsError=true -j 2 -M 4096`. Hooked into `desktopTest` and `check` whenever `entries` or `kotlinBytecodeClassPaths` is non-empty. Lifting is `--strict`: every method of every lifted class must lift, except the `<internal class>.<method>` entries listed in `lean { kotlinBytecodeUnliftedMethods }` (each of which must still exist and still fail to lift), and every `kotlinBytecodeClassPaths` entry must match compiled classes.

### Resource & Memory Caps
Lean elaboration and symbolic JVM stepping can allocate significant memory if unbounded:
- All Gradle Lean invocations (`generateLeanKotlin` and `verifyLeanJvmBytecode`) and `:lean-test-fixtures` desktop test runs pass `-j 2 -M 4096` (capping each `lean` process to 4 GiB and 2 threads).
- `verifyLean`, `generateLeanKotlin`, `verifyLeanJvmBytecode`, and the `desktopTest` task (whose `*VerificationTests` start `lake env lean`) acquire `leanTaskLimitingBuildService` (default `maxParallelUsages = 1`, configurable via `-Pcom.alexvanyo.composelife.maxConcurrentLeanTasks=...`) so multiple modules do not run concurrent Lean builds under Gradle `--parallel`.

### Verification Commands
```bash
# Verify Lean formalization across modules
./gradlew :session-value:verifyLean :geometry:verifyLean :algorithm:verifyLean \
  :navigation:verifyLean :resource-state:verifyLean :time-util:verifyLean \
  :ui-common:verifyLean :ui-cells:verifyLean :serialization:verifyLean :mosaic-calculator:verifyLean

# Lift compiled JVM bytecode and check JvmEquiv / KotlinJvmEquiv proofs
./gradlew :session-value:verifyLeanJvmBytecode :geometry:verifyLeanJvmBytecode \
  :algorithm:verifyLeanJvmBytecode :navigation:verifyLeanJvmBytecode \
  :resource-state:verifyLeanJvmBytecode :time-util:verifyLeanJvmBytecode \
  :ui-common:verifyLeanJvmBytecode :ui-cells:verifyLeanJvmBytecode \
  :serialization:verifyLeanJvmBytecode :mosaic-calculator:verifyLeanJvmBytecode

# Run Kotlin @Test bytecode verification suites on desktop JVM
./gradlew :algorithm:desktopTest --tests "*.BitComputationVerificationTests"
./gradlew :geometry:desktopTest --tests "*.GeometryExtensionsVerificationTests"

# Full check including proof verification, codegen checks, bytecode audits, and test suites
./gradlew check
```

---

## JVM Bytecode Semantics & Verifying Existing Kotlin

When verifying existing hand-written Kotlin (or validating the JVM bytecode produced for Lean-generated Kotlin), proofs connect directly to the compiled JVM instructions via the shared `jvm-lean` library and module-level bytecode harnesses.

### Shared JVM Semantics Library (`jvm-lean`)

Each Lean package (`session-value/lean`, `geometry/lean`, `algorithm/lean`, `navigation/lean`, `resource-state/lean`, `time-util/lean`, `ui-common/lean`, `ui-cells/lean`, `serialization/lean`, `mosaic-calculator/lean`) includes `jvm-lean` as a `[[lean_lib]]` dependency (`Jvm`):

| Module | Role |
|---|---|
| `Jvm.Instr` | Pure Lean AST (`JvmInstr`) of JVM bytecode instructions: stack/local loads & stores, `i32`/`i64`/`f32`/`f64` arithmetic & conversions, conditional/unconditional jumps, `tableswitch`/`lookupswitch`, primitive & object array accesses, field & method calls (`invokevirtual`, `invokespecial`, `invokestatic`, `invokeinterface`), object instantiation, `checkcast`/`instanceof`, `invokedynamic`, `athrow` (always fails closed: exception handlers are not modelled), and returns. Monitors and `dup_x*`/`dup2*`/`pop2` are not supported; the lifter rejects them. |
| `Jvm.Semantics` | Operational state & interpreter: `JvmVal Ext` (primitives `.i32`/`.i64`/`.f32`/`.f64`/`.bool`, references `.null`/`.heapRef`/`.str`/`.strArr`/`.allocRef`/`.pair`, boxed wrappers, and module extensions `.ext Ext`), `HeapObj Ext` (mutable typed primitive arrays, `objArray cls elems`, `stringBuilder`, `instance cls fields`), `JvmHeap Ext` (including static field tables), `JvmHooks Ext Heap` (module-specific extension hooks for `checkInstanceOf`, `checkCast`, `isSubtypeOf`, static/virtual/special/interface dispatch, and `beqExt`/`beqRefExt`), and fuel-bounded evaluators `runJvm` / `runJvmRes`. |
| `Jvm.FastExec` & `Jvm.Proofs` | Continuation/block-chunked evaluators (`runJvmValFast`, `runJvmResFast`, `stepBlockChunk`, `stepResBlockChunk`) proved equivalent to `runJvm`/`runJvmRes` (`runJvm_of_runJvmValFast0`, `runJvmRes_of_runJvmResFast0`), paired with opcode, call, and branch-normalization lemmas (`evalBranchInstrCons_*`, `evalResBranchInstrCons_*`, `runJvmResFast_invokestatic_step`, `runJvmResFast_invokeinterface_step`, `step_aastore`, etc.) so symbolic proofs avoid exploding `whnf`/`isDefEq`. |
| `Jvm.Tactics` | Meta-level normalization tactics (`normJvmBlkExpr`, `normJvmLocalsExpr`, `fastDropListEq`, `defaultEvalBranchThm`) used by module steppers (`jvm_step_blk0`, `jvm_step_blk`, etc.). |
| `Jvm.Audit` | Implements `#audit_jvm_equiv_axioms` and shared master-theorem audit helpers. |

Key safety & soundness invariants in `Jvm.Semantics`:
- **Fail-closed decoding**: `.asI32?`, `.asI64?`, `.asF32?`, `.asF64?` return `Option` (`none` traps execution to `none` instead of synthesizing bogus default integers or floats).
- **Division, bounds, and array checks**: Integer division/remainder by zero returns `none`; `newarray`/`anewarray` reject negative sizes (`slt 0#32`); primitive/object array loads/stores check bounds (`idx.toNat < size`) and `isArrayElemCompat`; `if_acmpeq`/`if_acmpne` use partial `JvmVal.refEq?` so undecidable/unboxed comparisons fail closed rather than silently evaluating equal.
- **Equality, strings, and conversions**: `Intrinsics.areEqual` and `toSet` deduplication only use the generic `JvmVal.beqVal` when `JvmVal.equalsModeled` holds for every operand (references to `.instance` heap objects may override `equals`, so they defer to the module hook instead of comparing addresses; dangling references are not modeled either). Theorems about code that compares generic values, such as ui-common's `TargetState.InProgress` constructor, `copy`, `map` and `equals`, therefore take `equalsModeled` hypotheses on those values; `Jvm.jvmVal_equalsModeled_set_instance` and `Jvm.jvmVal_equalsModeled_alloc` carry them across `putfield` and allocation. A JVM `char` that is a lone UTF-16 surrogate cannot be represented in a Lean `String`, so `char` concatenation, `StringBuilder.append(C)` and `concatToString` fail closed on it (`utf16UnitToChar?`, `decodeUtf16?`, which also combines surrogate pairs); `makeConcatWithConstants` recipes containing `\u0002` constants fail closed because the lifter does not carry bootstrap constants. `l2f` (`i64ToFloat32`) rounds once, directly from the integer, as the JVM does.
- **Trusted modelling limits**: `instanceof` returns a `Bool`, so a module's `isSubtypeOf`/`checkInstanceOf` tables must be complete for every class a proof tests (a missing supertype makes `instanceof` wrongly false rather than failing). Instance fields are keyed by name only (a subclass field that shadows a superclass field of the same name would share a slot), and the `ArrayList` iterator does not model `ConcurrentModificationException`. `dup`/`pop` do not reject category-2 values; this relies on the JVM verifier, which rejects such class files at load time (the lifter does not support `dup2`/`pop2`).
- **Module-specific hooks (`<module>/lean/JvmSemantics.lean`)**:
  - `session-value/lean/JvmSemantics.lean` (`svHooks`): Models `SessionValue` classes/helpers with `SessionValueExt` and `Unit` module heap.
  - `geometry/lean/JvmSemantics.lean` (`geomHooks`): Uses `Empty`/`Unit` (standard `JvmHeap` objects/arrays only) plus hooks for Compose `IntOffset` / `Offset` packing/boxing (`getX-impl`, `getY-impl`, `box-impl`, `unbox-impl`, `plus-qkQi6aY`, `IntOffset_jbKt.IntOffset`), `java/lang/Float.intBitsToFloat`, `java/lang/Math.floor`, `java/lang/Math.signum`, `IntOffset` `checkInstanceOf`/`checkCast`, and array-backed `java/lang/Iterable` / `java/util/List` / `ArrayList` / `Set`.
  - `algorithm/lean/JvmSemantics.lean` (`algHooks`): Adds `AlgExt` / `AlgHeap` for `MacroCell` nodes, `Arena` refs, and `ULongArray` refs alongside `JvmHeap`. Note the documented soundness boundary for `algorithm/lean`: `.arena*Ref` and `.u64Ref` fast paths use Lean's total `Array.get!`/`set!` (while `ULongArray.constructor-impl(I)[J` checks negative sizes fail-closed and arithmetic/bit operations use fail-closed `.asI32?`/`.asI64?`), whereas generic `HeapObj` arrays in `jvm-lean` enforce full bounds and element compatibility checks.
    For the hand-written Kotlin in `KotlinJvmBytecode` (`HashLifeComputationKt`, `MacroCellCoordinatesKt`, `GameOfLifeStepKt`, `CellWindow`), `mkAlgKotlinHooks resolveProg depth fuel` extends these hooks: calls between lifted classes run the callee's lifted program (looked up by `"<Class>.<method>:<descriptor>"`, see `proofs/KotlinJvmEquiv/AlgKotlinProgs.lean`), and leaf hooks model Compose `IntOffset`/`IntRect`, `LinkedHashSet`/`ArrayList`/`IntRange`, `getMooreNeighbors` (geometry's verified model) and the Lean-compiled `f_Algorithm_*` functions, with each trusted assumption documented in `JvmSemantics.lean`.
  - `navigation/lean/JvmSemantics.lean`: Models `BackstackEntry` / `BackstackState` / `MutableBackstackState` value payloads (`NavValue`, `NavExt`) and map/list operations for `BackstackNavigationKt`.
  - `resource-state/lean/JvmSemantics.lean`: Models `ResourceState` sealed hierarchy (`Loading`, `Success`, `Failure`), payload values (`RsVal`), and `Pair` / lambda hooks for `ResourceStateKt`.
  - `time-util/lean/JvmSemantics.lean`: Models `kotlinx.datetime` `Instant` / `DateTimePeriod` / `DateTimeUnit` / `TimeZone` / `Clock` plus Compose `Composer` slot-table helpers (`composerEmpty`, `composer`, `stateRef`, `remember` / `LaunchedEffect` / `mutableStateOf`) to verify `PeriodUntilKt` including its `@Composable` wrappers on initial composition.
  - `ui-common/lean/JvmSemantics.lean`: Models `TargetState` (`Single`, `InProgress`, `copy`, `map`, `equals`), `Easing` / `EasingPiecewise` (`UiEasing`, `UiExt`), stable `sortedWith`, and module-internal static-call dispatch.
  - `mosaic-calculator/lean/JvmSemantics.lean`: Combines `ComposeSemantics` and `MosaicSemantics` with `CalcExt` to verify a handwritten Kotlin calculator model and its `@Composable` Mosaic UI.

### Bytecode Lifting (`script/jvm-bytecode2lean.py`)

`script/jvm-bytecode2lean.py` disassembles `.class` files using `javap -v -p` and emits pure `List JvmInstr` Lean definitions. No semantics live in the Python script; it supports `--instr-type`, `--require` (to fail if expected method symbols are missing), `--strict` / `--allow-unlifted` (fail on any method outside the instruction subset unless explicitly listed), and constant-pool decoding (`ldc`, `ldc2_w`, `tableswitch`, `lookupswitch`). Member references inside a class are qualified with the class's full internal name (from `javap`'s `this_class`), exactly like references from other classes.

Names never depend on which other classes are lifted or in what order. Overloads within one class are numbered `_1`, `_2`, … in class-file order. Hand-written Kotlin (`KotlinJvmBytecode`, and the test-time `RealJvmBytecode`) is lifted with `--qualify-names`: every definition is `<ClassSimpleName>_<method>_prog` (`<Class>_init_prog` for constructors, `<Class>_clinit_prog` for static initializers), so the Gradle and test lifts always agree. Lean-generated classes (`JvmBytecode`) keep `<method>_prog` (`clinit_<Class>_prog` for static initializers) and prefix the class name only on a name that several classes produce; a later collision therefore removes the unprefixed name (a compile error) rather than silently re-pointing it.

### Workflow: Proving an Existing Kotlin Function

Follow these five steps to verify hand-written Kotlin without rewriting the production implementation into Lean:

1. **Configure bytecode lifting in `<module>/build.gradle.kts`**:
   Add the target `.class` path under the `lean` block (only desktop JVM `.class` files under `build/classes/kotlin/desktop/main` are inspected):
   ```kotlin
   lean {
       target = "Geometry:static"
       packageName = "com.alexvanyo.composelife.geometry"
       kotlinBytecodeClassPaths.add("com/alexvanyo/composelife/geometry/GeometryExtensionsKt.class")
   }
   ```
   Running `./gradlew :<module>:verifyLeanJvmBytecode` lifts those methods into `<module>/build/generated/lean/jvm/KotlinJvmBytecode.lean`.

2. **Write an independent Lean model (`<module>/lean/models/<Name>Model.lean`)**:
   Model the intended behavior directly from first principles and Kotlin semantics using fixed-width/list/grid types (never using Lean-to-Kotlin codegen output as the spec). Export any helper types or predicates needed downstream.

3. **Prove properties of the model (`<module>/lean/proofs/<Name>ModelProofs.lean`, `<module>/lean/theorems/<Name>ModelTheorems.lean`)**:
   State clear domain guarantees (invariants, round-trips, metric inequalities, exact Conway transition equivalence) with zero `sorry` and zero custom axioms (using `bv_check` with stored `.lrat` certificates for bit-level proofs).

4. **Prove JVM bytecode equivalence (`<module>/lean/proofs/KotlinJvmEquiv/<Name>.lean` + `proofs/KotlinJvmEquiv.lean`)**:
   - Prove that executing `runJvm` / `runJvmRes` on `<fn>_prog` returns the exact result/heap effect of your Lean model (and if static fields/lookup tables are used, prove `<clinit>_prog` establishes a heap invariant such as `HasQuadInfoLut` or `HasGeometryNeighborLuts`, and assume that invariant on methods reading the static fields).
   - End `proofs/KotlinJvmEquiv.lean` with:
     ```lean
     #audit_jvm_equiv_axioms <Module>.KotlinJvmVerification <Module>.KotlinJvmBytecode
     ```
     This build-time command fails if any verification theorem relies on `sorry` or non-standard axioms, or if any lifted `*_prog` in the target class lacks an equivalence theorem: one whose conclusion runs the program (`runJvm*`) and none of whose hypotheses already assume something about running it.

5. **Expose theorems as standard Kotlin `@Test` cases (`:lean-test-fixtures`)**:
   Add a `*VerificationTests.kt` test class in `<module>/src/desktopTest/...` using `JvmBytecodeVerificationSpec` and `verifyTheorem` from `lean-test-fixtures`:
   - `JvmBytecodeLeanVerifier.verifyBytecodeTheorem` loads the **live `.class` resource from the test runtime classpath**, verifies its `0xCAFEBABE` header, lifts it via `script/jvm-bytecode2lean.py` into `RealJvmBytecode`, and compiles it to an `.olean`.
   - It then elaborates the theorem stated in the `@Test` against `RealJvmBytecode` (using `lake env lean -DwarningAsError=true -j 2 -M 4096`), rejecting forbidden constructs (`sorry`, `admit`, `axiom`, `bv_decide`, `unsafe`, `partial`, `initialize`, anything that runs metaprograms (`run_meta`, `run_elab`, `run_cmd`, `run_tac`, `by_elab`, `#eval`, `#exit`, `elab`, `macro`, `syntax`), `set_option debug.*`/`trust*`, and `implemented_by`/`extern`/`csimp` attributes) via `validateLeanBody`, checking via `run_meta` that the theorem is non-trivial, that its conclusion runs (`runJvm*`) a `RealJvmBytecode` program, and that no hypothesis assumes running one, and asserting `#print axioms` reports only standard core axioms (`propext`, `Classical.choice`, `Quot.sound`) or LRAT `bv_check` axioms (`._native.bv_decide.`).
   - The convention plugin declares the module's Lean sources (`moduleLeanInputFiles`), the shared `jvm-lean` sources, and `script/jvm-bytecode2lean.py` as `desktopTest` inputs, so changing a proof, model, or hook reruns these suites instead of reusing an up-to-date or build-cached result.
   - See [BitComputationVerificationTests.kt](file:///home/xela/Projects/composelife/algorithm/src/desktopTest/kotlin/com/alexvanyo/composelife/algorithm/BitComputationVerificationTests.kt) and [GeometryExtensionsVerificationTests.kt](file:///home/xela/Projects/composelife/geometry/src/desktopTest/kotlin/com/alexvanyo/composelife/geometry/GeometryExtensionsVerificationTests.kt) for complete examples.

---

## Axiom Auditing

Every master theorem must depend only on standard Lean foundational axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`

plus the axioms that `bv_check` adds. Each `bv_check` (like `bv_decide`) adds an axiom such as
`foo._native.bv_decide.ax_1_5`, which asserts that Lean's compiled LRAT checker accepted the stored certificate.
This trust in the compiled checker is accepted for bit-level proofs (see [Bit-Level Proofs](#bit-level-proofs)).

Master theorems must never depend on `sorry`, custom axioms, or `native_decide`, which trusts arbitrary compiled
code. A plain `grep axiom` does not find natively evaluated axioms; only `#print axioms` does.

Each package checks this on every build. Its `AxiomAudit.lean` root module runs `#audit_master_theorem_axioms`,
which collects the axioms of every theorem in the master theorem and mutation modules and fails the build if any
is neither standard nor a `bv_check` axiom (named `<declaration>._native.bv_decide.ax_<n>` and stating
`verifyBVExpr … = true`) whose certificate the audit re-checks by running the compiled LRAT checker again (`Jvm.isVerifiedJvmBvCheckAxiom`), so an axiom of that shape added by a metaprogram with a false certificate is rejected. Because a hand-written `axiom` could copy that name and statement, `checkLeanBvCheck`
also rejects every `axiom` declaration in the Lean sources. `verifyLean` (`lake build --wfail`)
therefore fails on any other axiom. Additionally, `#audit_jvm_equiv_axioms <VerifNs> <BytecodeNs>` (defined in `jvm-lean/Jvm/Audit.lean` and run by `proofs/JvmEquiv.lean` and `proofs/KotlinJvmEquiv.lean`) checks that no custom axioms or `sorry` are used in bytecode equivalence namespaces and that every lifted `*_prog` has a non-trivial equivalence theorem. To inspect a single theorem:
```lean
#print axioms computeNextGen4x4_correct
```

The same module also runs `#audit_master_theorem_names`, which checks the `X` / `X_Impl` naming pattern of the
master theorems (see [Master Theorems](#3-master-theorems-componenttheoremslean-or-theoremslean)).

---

## Pruning Dead Proofs

A theorem in a proof module that no master theorem depends on proves nothing about the compiled code. Such
theorems pile up as proofs are restructured (superseded lemmas, abandoned approaches, aliases of old names), and
they can hide weak or circular statements that look load-bearing. Prune them with
`script/prune-dead-lean-proofs.py`:

```bash
# From the repository root, after `lake build` in the package:
script/prune-dead-lean-proofs.py algorithm/lean            # report dead theorems
script/prune-dead-lean-proofs.py algorithm/lean --defs     # also report dead definitions in specs and models
script/prune-dead-lean-proofs.py algorithm/lean --apply    # delete what it reports
```

How it works:
1. It loads every module in the package's `lakefile.toml` roots into a temporary Lean file and runs it with
   `lake env lean`.
2. The roots of the search are the master theorems (every theorem in a module named `*Theorems` or `theorems.*`)
   and the mutation proofs (modules named `*Mutations`), which are kept as evidence that the theorems are strong.
3. It marks as live everything reachable from the roots by following the constants used in each declaration's
   type and value. This covers lemmas used by `simp`, `omega`, `decide` and other tactics, because they appear
   in the elaborated proof terms. Theorem bodies are read with `ConstantInfo.value? (allowOpaque := true)`.
4. It reports every theorem in a proof module (`proofs.*`, `*Proofs`) that is not live. With `--defs` it also
   reports definitions in specification and model modules (`*Defs`, `models.*`). Production modules, structure
   projections, derived instances, elaborator-generated auxiliary declarations, and tactics, macros and their
   meta-level helpers are never reported.
5. It keeps any reported declaration whose name still appears in source text outside the reported
   declarations themselves. A lemma that `simp` or `dsimp` uses by `rfl` leaves no trace in the proof term.
6. With `--apply` it deletes each reported declaration, together with its docstring, attributes and
   `set_option ... in` lines, up to the next top-level command.

Deleting dead declarations never breaks a live one. It can still leave aliases (`abbrev foo := @deadTheorem`),
comments or modules that are now empty. After `--apply`:
1. Run `lake build --wfail`, and fix what references deleted names.
2. Rerun the script until it reports nothing. Removing a dead alias or definition can expose more dead code.
3. Delete modules left without declarations, and remove them from imports and `lakefile.toml`.
4. Review the diff. If a deleted theorem states something worth guaranteeing, restore it and promote it to a
   master theorem instead.

Before removing a master theorem, check what it is for. A master theorem whose hypothesis restates its
conclusion (for example, assuming the compiled step function agrees with the model step function) should be
removed. The lemmas it alone kept alive then become dead and can be pruned.

---

## Proof Tactics Guide

Tactics are used only in implementation proof files (`*Proofs.lean`, `proofs/*.lean`), never in production, `*Defs.lean`, or `*Theorems.lean` files.

### Choosing a tactic

| Goal shape | Tactic |
| :--- | :--- |
| Linear `Nat`/`Int` arithmetic, modulo, bounds | `omega` |
| Linear inequalities over ordered fields (`ℚ`, `ℝ`) | `linarith` (`nlinarith` for products) |
| Ring equalities | `ring` |
| `0 < x`, `0 ≤ x`, `x ≠ 0` | `positivity` |
| Numeric literals | `norm_num` |
| Small, finite, decidable propositions | `decide` |
| Rewriting with known equations | `simp`, `simp_all` |
| Mixed equalities, case splits, and arithmetic (core Lean) | `grind` |
| Branching on `if`/`match` | `split_ifs`, `split` |
| Destructuring hypotheses, induction | `rcases`/`obtain`, `cases`, `induction` |
| Propositional/structural leaves after the above | `aesop` |

### When to use `aesop`

`aesop` is a proof-search tactic: it normalizes with `simp`, then applies safe and unsafe rules (constructors, `cases`, hypotheses) until the goal closes. It either closes the goal or fails, so it never leaves a half-finished state.

Use it for:
- Leaves made up of conjunctions, disjunctions, existentials, set membership, or inductive predicates, such as `split_ifs <;> aesop` or `cases h <;> aesop`.
- Goals that need `simp` plus a few `constructor`, `cases`, or `exact` steps.

Avoid it for:
- Arithmetic. Use `omega` or `linarith` first.
- Large goals, as a first resort. Split the goal first, then call `aesop` on the leaves.
- Goals that depend on unfolding your own definitions. `unfold` them first, or pass `aesop (add norm unfold foo)`.

### Practices

- Run `aesop?` while developing. It prints a `Try this` script. Replace a slow or flaky `aesop` call with that script to keep CI builds fast and stable.
- Extend the rule set locally with `aesop (add safe foo)` or `aesop (add norm simp bar)`. Use `@[aesop safe]` attributes sparingly, and only in proof files.
- If `aesop` fails, read the remaining goal in its error. Then try `simp_all`, `grind`, or manual steps.
- Remove exploratory tactics (`exact?`, `apply?`, `rw?`, `simp?`, `aesop?`) before committing.

### Availability

`aesop` is a separate Lake package, also pulled in by Mathlib.
- `geometry/lean` requires it explicitly in `lakefile.toml` and imports it with `import Aesop`.
- `algorithm/lean` and `session-value/lean` depend only on core Lean, so `aesop` is not available there. Use `omega`, `simp`, `decide`, and `grind`.
- To use it in another package, add a `[[require]]` for `aesop` (`git = "https://github.com/leanprover-community/aesop"`, `rev = "master"`). Import `Aesop` only from proof files so `lake build <Component>:static` stays free of it.

### Bit-Level Proofs

Prove fixed-width bit-manipulation facts (`UInt32`/`UInt64`/`BitVec` goals built from shifts, masks, `+`, `*`,
comparisons and `cpop`) with `bv_decide`, and commit them as `bv_check` with a stored LRAT certificate so builds
check the stored proof instead of running the SAT solver:

1. Write `bv_decide?` where the proof goes, after unfolding the definitions involved. State one goal per call: a
   conjunction proved by one `bv_decide?` is cheaper than many calls, and a `bv_decide?` reached by several goals
   (for example after `<;>`) cannot be stored, because each goal needs its own certificate.
2. Once the package's dependencies are built, run
   ```bash
   script/lean-bv-check.py algorithm/lean proofs/HashLifeKernelProofs.lean
   ```
   It elaborates the file, moves each certificate into `proofs/lrat/<File>.<full declaration name>[-<n>].lrat`, and replaces
   each `bv_decide?` with the `bv_check "lrat/..."` that reads it.
3. Commit the `.lrat` files with the Lean file. When a goal proved by `bv_check` changes, put `bv_decide?` back in
   its place and rerun the script.

Do not leave `bv_decide` or `bv_decide?` in committed proofs. They add the same axioms as `bv_check`, so the axiom
audit cannot catch them; `checkLeanBvCheck` (run by `verifyLean`) fails the build instead. For a fact needed at
many goals of one tactic block, prove a general lemma once (with `bv_check` or plain `simp`) and apply it at each
goal.
