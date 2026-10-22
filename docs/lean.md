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
  - Contains **zero proof bodies** (no `by`, `sorry`, or inline tactics).
  - Every master theorem delegates directly to its `_Impl` counterpart:
    ```lean
    theorem computeNextGen4x4_correct (w : UInt32) (h : w < 65536) :
        decode4x4Center (computeNextGen4x4 w) = naiveCenter2x2 (decode4x4 w) :=
      computeNextGen4x4_correct_Impl w h
    ```

### 4. Implementation Proofs (`<Component>Proofs.lean` or `proofs/*.lean`)
- **Purpose**: Tactical proofs, intermediate lemmas, induction arguments, and solver invocations (`omega`, `linarith`, `ring`, `decide`, `bv_check`).
  - Implements the `..._Impl` theorems referenced in master theorems.
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
     stops and emits each live cell exactly once. `fitsInIntRange` runs the same cursor over the regions past
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

plus the axioms that `bv_check` adds. Each `bv_check` (like `bv_decide`) adds an axiom such as
`foo._native.bv_decide.ax_1_5`, which asserts that Lean's compiled LRAT checker accepted the stored certificate.
This trust in the compiled checker is accepted for bit-level proofs (see [Bit-Level Proofs](#bit-level-proofs)).

Master theorems must never depend on `sorry`, custom axioms, or `native_decide`, which trusts arbitrary compiled
code. A plain `grep axiom` does not find natively evaluated axioms; only `#print axioms` does.

Each package checks this on every build. Its `AxiomAudit.lean` root module runs `#audit_master_theorem_axioms`,
which collects the axioms of every theorem in the master theorem and mutation modules and fails the build if any
is neither standard nor a `bv_check` axiom (named `<declaration>._native.bv_decide.ax_<n>` and stating
`verifyBVExpr … = true`). Because a hand-written `axiom` could copy that name and statement, `checkLeanBvCheck`
also rejects every `axiom` declaration in the Lean sources. `verifyLean` (`lake build --wfail`)
therefore fails on any other axiom. To inspect a single theorem:
```lean
#print axioms computeNextGen4x4_correct
```

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
