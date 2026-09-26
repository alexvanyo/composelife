# Formal Verification of `session-value` in Lean 4

This directory contains the formal specification and mechanized proofs for the state management,
synchronicity, and concurrency logic implemented in the `session-value` Kotlin Multiplatform module.

## Formalization Structure

- **`SessionValue/Basic.lean`**: Primitives including `Uuid`, `SessionValue α`, and `LocalSessionInfo`.
- **`SessionValue/StateMachine.lean`**: Model of the mutable internal state of `SessionValueHolderImpl`,
  its core inductive invariant `ValidState`, and transition steps (`stepSetValue`, `stepSetValueFromUpstream`).
- **`SessionValue/Mapping.lean`**: Proof of functorial laws (`map id = id`, composition) and round-trip
  fidelity for `SessionValueHolder.map`.
- **`SessionValue/AsyncBatching.lean`**: Formalization of `rememberAsyncSessionValueHolder`, including
  stale update queue pruning across session changes and atomicity of chained Compare-And-Set (CAS) batching.
- **`SessionValue/Properties.lean`**: Master verification theorems:
  - **Theorem 1 (`initialState_valid`)**: Initial state satisfies the `ValidState` invariant.
  - **Theorem 2 (`stepSetValue_preserves_valid`)**: User edits preserve `ValidState`.
  - **Theorem 3 (`stepSetValueFromUpstream_preserves_valid`)**: Upstream updates preserve `ValidState`.
  - **Theorem 4 (`local_synchronicity`)**: Zero-latency local UI responsiveness upon setting values.
  - **Theorem 5a & 5b (`id_stability_localSessionId`, `id_stability_preLocalSessionId`)**: Invariant stability
    when promoting an inactive session to an active editing session.
  - **Theorem 6a & 6b (`upstream_echo_keeps_active`, `upstream_echo_up_to_date`)**: Upstream echoes of local
    updates keep local sessions active and converge to up-to-date status when matching the latest valueId.
  - **Theorem 7 (`upstream_conflict_invalidates`)**: Remote/foreign upstream updates cleanly invalidate local
    uncommitted state, resetting to inactive and preventing split-brain states.
  - **Theorem 8 (`cas_expected_soundness`)**: Emitted CAS prerequisites always match the held session value.

## Building and Checking

To check all proofs with Lean 4:

```bash
lake build
```

Or via Gradle from the repository root:

```bash
./gradlew :session-value:verifyLean
```
