# Lean 4 Formal Verification Architecture

ComposeLife uses [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4) to formally specify and verify core data structures, state machines, and algorithms. Verified Lean code is compiled via `lake` into static C libraries and bridged to Kotlin Multiplatform via C/JNI bindings.

This document describes the standard 4-role architecture, file organization, naming conventions, and build configurations required for all Lean projects in the repository.

---

## The 4-Role Architecture

To keep production code clean, maintain fast compilation, and clearly distinguish between formal specifications, master guarantees, and tactical proofs, every Lean component is structured into four distinct roles:

```
┌────────────────────────────────────────────────────────┐
│  1. Production Executable Code                         │
│     (<Component>.lean, <Component>/*.lean)             │
│     - Pure executable definitions and algorithms       │
│     - 0 theorems, 0 proofs, 0 heavy tactic imports     │
│     - Compiled to C for FFI                            │
└────────────────────────────────────────────────────────┘
                           ▲
                           │ specifies behavior
┌──────────────────────────┴─────────────────────────────┐
│  2. Specification Definitions                          │
│     (<Component>Defs.lean)                             │
│     - Non-executable definitions & predicates          │
│     - Continuous models, invariants, relations         │
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
- **Purpose**: Defines executable types, pure algorithms, and FFI bridging functions that run in production.
- **Rules**:
  - Must contain **executable code only**.
  - Must contain **no proofs or non-equational theorems** (with the exception of trivial constructor/equational lemmas like `cell_beq_def ... := rfl`).
  - Must **not** import proof-only libraries (e.g. `Mathlib.Tactic.*`, heavy analysis modules) that would bloat production compilation or runtime dependencies.

### 2. Specification Definitions (`<Component>Defs.lean`)
- **Purpose**: Defines the mathematical concepts, continuous models, inductive invariants, bounding boxes, or transition relations necessary to state properties of the code.
- **Rules**:
  - Contains definitions (`def`, `inductive`, `structure`, `class`) and predicates (`... : Prop`), but **no proofs**.
  - Provides a single point of truth for mathematical specifications imported by both master theorem files and tactical proof files.

### 3. Master Theorems (`<Component>Theorems.lean` or `theorems/*.lean`)
- **Purpose**: Represents the clean, readable public interface of the formal verification. Anyone reviewing the formal verification can read these files to see exactly what properties were proven without getting lost in tactic scripts.
- **Rules**:
  - Contains **only meaningful, important theorems** specifying the code.
  - Contains **zero proof bodies** (no `by` tactics, `sorry`, or inline proofs).
  - Every master theorem delegates directly to an analogous `_Impl` theorem:
    ```lean
    theorem stepGrid_preserves_finite (g : Grid) (h : g.Finite) :
        (stepGrid g).Finite :=
      stepGrid_preserves_finite_Impl g h
    ```
  - **Hierarchy Rule**:
    - **Single Domain / Component**: Placed in a single top-level file: `<Component>Theorems.lean` (e.g., `SessionValueTheorems.lean`, `GeometryTheorems.lean`).
    - **Multiple Modules**: Placed in a `theorems/` subfolder with modular files (e.g., `theorems/PatternsTheorems.lean`, `theorems/HashLifeTheorems.lean`), re-exported by a top-level `<Component>Theorems.lean`.

### 4. Implementation Proofs (`<Component>Proofs.lean` or `proofs/*.lean`)
- **Purpose**: Contains all tactical proofs, sub-lemmas, case analyses, and inductive arguments required to discharge the master theorems.
- **Rules**:
  - Contains the definitions of all `..._Impl` theorems referenced in `*Theorems.lean`.
  - May freely use heavy tactical solvers (`omega`, `linarith`, `ring`, `aesop`, `positivity`). See the [Proof Tactics Guide](#proof-tactics-guide).
  - May be decomposed across multiple submodules and directories when proofs grow large.
  - **Hierarchy Rule**:
    - **Single Domain / Component**: Placed in `<Component>Proofs.lean` (e.g., `SessionValueProofs.lean`).
    - **Multiple Modules**: Placed in a `proofs/` subfolder (e.g., `algorithm/lean/proofs/` or `geometry/lean/proofs/`), re-exported by `<Component>Proofs.lean`.

---

## Project Structure Examples

### 1. Simple / Single Component: `session-value`
In `session-value/lean`, there is a single domain (session state machine and mutations):
```
session-value/lean/
├── SessionValue.lean            # Root executable module (imports submodules)
├── SessionValueDefs.lean        # Specification definitions (valid state predicates)
├── SessionValueTheorems.lean    # Master theorems (delegating to *_Impl)
├── SessionValueProofs.lean      # Complete tactical proofs of all *_Impl theorems
├── SessionValue/
│   ├── StateMachine.lean        # Pure executable state machine
│   └── Mutations.lean           # Pure executable mutations
└── lakefile.toml
```

### 2. Multi-Module Component: `algorithm`
In `algorithm/lean`, multiple distinct subsystems exist (BitComputation, MacroCell, HashLife, Patterns). Theorems and proofs are split into dedicated subfolders:
```
algorithm/lean/
├── Algorithm.lean               # Root executable module
├── AlgorithmDefs.lean           # Shared specification definitions
├── AlgorithmTheorems.lean       # Master orchestrator exporting all theorems
├── AlgorithmProofs.lean         # Master orchestrator exporting all proofs
├── Algorithm/
│   ├── Basic.lean               # Executable grid representation
│   ├── BitComputation.lean     # Executable bitboard operations
│   ├── MacroCell.lean           # Executable quadtree nodes
│   ├── MacroCellHash.lean       # Executable hash tables
│   ├── HashLife.lean            # Executable HashLife algorithm
│   └── Patterns.lean            # Executable Game of Life patterns
├── theorems/
│   ├── BitComputationTheorems.lean
│   ├── MacroCellTheorems.lean
│   ├── MacroCellHashTheorems.lean
│   ├── HashLifeTheorems.lean
│   ├── PatternsTheorems.lean
│   └── PropertiesTheorems.lean
├── proofs/
│   ├── BitComputationProofs.lean
│   ├── MacroCellProofs.lean
│   ├── MacroCellHashProofs.lean
│   ├── HashLifeProofs.lean
│   ├── PatternsProofs.lean
│   └── PropertiesProofs.lean
└── lakefile.toml
```

### 3. Continuous Geometry & Floating-Point Component: `geometry`
In `geometry/lean`, continuous raymarching algorithms, floating-point error bounds, and waypoint decompositions are verified:
```
geometry/lean/
├── Geometry.lean                # Root executable module
├── GeometryDefs.lean            # Specification definitions (intervals, Hausdorff metric, waypoints)
├── GeometryTheorems.lean        # Master theorems (clearance equivalence & Hausdorff bounds)
├── GeometryProofs.lean          # Master proof aggregator & reduction proofs
├── Geometry/
│   ├── Basic.lean               # Executable Point, Cell, and Grid definitions
│   ├── LineSegment.lean         # Executable ideal rational raymarching
│   ├── FloatModel.lean          # Executable floating-point raymarching
│   └── Bridge.lean              # C-ABI export functions for Kotlin FFI
├── proofs/
│   ├── Interval.lean        # Parameter interval analysis
│   ├── RayMarchStep.lean    # Single-step transition lemmas
│   ├── Soundness.lean       # Soundness of raymarching
│   ├── Completeness.lean    # Completeness of raymarching
│   ├── FloatSemantics.lean  # Floating-point arithmetic semantics
│   ├── FloatBounds.lean     # Coordinate bounds & step classifications
│   ├── FloatAnalysis.lean   # Dyadic/Real rounding and error bounds
│   ├── FloatProperties.lean # Clearance equivalence & Hausdorff bound proofs
│   └── SegmentBound/        # Inductive sub-segment waypoint proofs
│       ├── Waypoints.lean
│       ├── PointBound.lean
│       ├── MiniSegment.lean
│       └── Hausdorff.lean
└── lakefile.toml
```

---

## Lake Build Configuration (`lakefile.toml`)

To ensure Lake and CI check all definitions, master theorems, and proofs during builds, configure the `roots` option in `lakefile.toml` of the Lean package:

```toml
[package]
name = "Algorithm"
version = "0.1.0"

[[lean_lib]]
name = "Algorithm"
roots = [
  "Algorithm",
  "AlgorithmDefs",
  "AlgorithmTheorems",
  "AlgorithmProofs",
]

[[lean_lib]]
name = "AlgorithmFFI"
srcDir = "."
roots = ["Algorithm"]
```

This guarantees:
1. `lake build <Component>:static` compiles only the production executable library into static C objects for FFI.
2. `lake build <Component>Theorems` verifies that all master theorems compile cleanly and their `_Impl` proofs hold.

---

## Coding Style & Verification Standards

1. **Apache 2.0 Header**: All `.lean` files must start with the standard Apache 2.0 license comment (from `config/license.template`).
2. **No Ambiguous Mathlib Notations**: Avoid declaring `local notation "ℚ" => Rat` or `local notation "ℤ" => Int` in files where Mathlib is imported. Mathlib already exports `ℚ` and `ℤ`; redeclaring them creates ambiguity errors.
3. **No Proofs in Master Theorem Files**: Master theorems in `*Theorems.lean` must strictly delegate to `:= <theorem>_Impl`. They should never contain tactic blocks or `by` tactics.
4. **Zero Custom Axioms & Zero `sorry`s on Master Theorems**: Master theorems must depend only on standard Lean foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). Verify with `#print axioms <theorem_name>`.
5. **Gradle Integration**: In root directory, verify that Gradle runs all Lean checks and Kotlin tests:
   ```bash
   ./gradlew :session-value:check
   ./gradlew :algorithm:check
   ./gradlew :geometry:check
   ```

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
