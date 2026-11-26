# lean-test-fixtures

Desktop JVM test harness (`JvmBytecodeVerificationSpec`, `JvmBytecodeLeanVerifier`, `verifyTheorem`) for running Lean 4 JVM bytecode equivalence proofs as standard Kotlin `@Test` suites.

At test time, it loads the live `.class` resource from the test runtime classpath, lifts it via `script/jvm-bytecode2lean.py` into `RealJvmBytecode`, and elaborates the theorem statements in Lean while rejecting forbidden constructs (`sorry`, `axiom`, `bv_decide`, metaprograms, etc.) and auditing `#print axioms`.

See [`docs/lean.md`](../docs/lean.md#workflow-proving-an-existing-kotlin-function) for usage details.
