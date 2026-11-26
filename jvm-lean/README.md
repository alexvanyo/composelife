# jvm-lean

Shared Lean 4 operational semantics library (`Jvm`) for verifying compiled JVM `.class` bytecode in ComposeLife.

See [`docs/lean.md`](../docs/lean.md#jvm-bytecode-semantics--verifying-existing-kotlin) for full architecture documentation.

## Modules

- `Jvm/Instr.lean`: Pure Lean AST (`JvmInstr`) of supported JVM bytecode instructions.
- `Jvm/Semantics.lean`: Fail-closed operational state, values (`JvmVal`), heap (`JvmHeap`, `HeapObj`), extension hooks (`JvmHooks`), and fuel-bounded evaluators (`runJvm`, `runJvmRes`).
- `Jvm/FastExec.lean` & `Jvm/Proofs.lean`: Block-chunked symbolic evaluators proved equivalent to `runJvm` / `runJvmRes`, plus opcode/branch/call normalization lemmas.
- `Jvm/Tactics.lean`: Meta-level normalization tactics used by module bytecode steppers.
- `Jvm/Audit.lean`: `#audit_jvm_equiv_axioms` and master-theorem axiom/name auditing commands.
