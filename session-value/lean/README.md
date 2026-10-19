# Formal Verification of `session-value` in Lean 4

This directory contains the formal specification and mechanized proofs for the state management,
synchronicity, and concurrency logic implemented in the `session-value` Kotlin Multiplatform module.

## Formalization Structure

Adhering to the 4-role formalization architecture defined in `docs/lean.md`:

### Role 1: Production Executable Code (`SessionValue/`)
- **`SessionValue/Basic.lean`**: Primitives including `Uuid`, `SessionValue α`, and `LocalSessionInfo`, and the
  stale-update predicate `isCurrentSessionUpdate` used by the Kotlin async update queue.
- **`SessionValue/StateMachine.lean`**: Core state machine and transitions (`stepSetValue`, `stepSetValueFromUpstream`).

### Role 2: Specification Definitions (`SessionValueDefs.lean`)
- Inductive invariant `ValidState` (including inactive soundness and session freshness).
- Compare-and-set models (`casApplyWith`, `casApplyAllWith`) parameterized by the upstream's acceptance test,
  with the two policies used in the app (`fullMatch`, `idMatch`), plus `CASChained` and `batchUpdate`.
- The async update queue of `rememberAsyncSessionValueHolder`: its pruning (`pruneStaleUpdates`), its invariant
  (`QueueInv`), and its reachable states under any interleaving of edits, upstream changes and flushes
  (`AsyncReachable`).
- State mapping functor (`State.map`).

### Role 3: Master Theorems (`SessionValueTheorems.lean`)
- **Theorem 1 (`initialState_valid`)**: Initial state satisfies the `ValidState` invariant with fresh session ID.
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
- **Theorem 8b (`cas_emission_soundness`)**: Emitted CAS updates target valid expected session IDs and preserve local session ID.
- **Theorem 9 (`batch_cas_equivalence`)**: For any upstream whose compare-and-set accepts a value as matching
  itself, a chained queue of any length has the same outcome as its single batched update.
- **Theorem 9a (`cas_policies_reflexive`)**: Both compare-and-set policies used in the app satisfy that condition.
- **Theorem 10a (`asyncReachable_invariant`)**: In every reachable state of the async holder, `ValidState` holds and
  the update queue is a block of stale updates followed by the chained updates of the current local session.
- **Theorem 10b (`pruneStaleUpdates_exact`)**: Pruning removes exactly the stale updates.
- **Theorem 10c (`async_batch_sound`)**: The batched update the async holder sends has the same outcome as sending
  each update of the current session in order, and writes exactly the value the holder shows.
- **Theorem 11a, 11b & 11c (`sessionValue_map_id`, `sessionValue_map_comp`, `mapped_setValue_roundtrip`)**: Functorial
  laws for `SessionValue.map`, and the mapped holder shows exactly the value and value id that were set.

### Role 4: Implementation Proofs (`SessionValueProofs.lean`, `proofs/`)
- Mechanized tactic proofs for all master theorems.
- **`proofs/Mutations.lean`**: Mutation proofs. Each mutant is a plausible buggy variant (echo handling, conflict
  handling, the pre-5e57f71 state restoration, and the earlier stale-update pruning rule), and each proof shows the
  mutant violates the property a master theorem proves for the real implementation.

The async update queue loop, the flush loop and `MappedSessionValueHolder` are hand-written Kotlin. Their Lean
counterparts (`AsyncReachable`, `State.map`) are models; the stale-update decision itself is compiled from Lean.

## Building and Checking

To check all proofs with Lean 4:

```bash
lake build
```

Or via Gradle from the repository root:

```bash
./gradlew :session-value:verifyLean
```
