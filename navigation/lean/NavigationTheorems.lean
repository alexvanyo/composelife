/-
 * Copyright 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 -/

import Navigation.Backstack
import NavigationDefs
import NavigationProofs

namespace Navigation

/--
Theorem 1: `BackstackEntry.mkEntry` constructs an entry whose `value`, `previous`, and `id` accessors
return the exact arguments supplied.
-/
theorem mkEntry_spec (val : α) (prev : Option (BackstackEntry α)) (id : Uuid) :
    (BackstackEntry.mkEntry val prev id).value = val ∧
    (BackstackEntry.mkEntry val prev id).previous = prev ∧
    (BackstackEntry.mkEntry val prev id).id = id :=
  mkEntry_spec_Impl val prev id

/--
Theorem 2a: `iterateBackstackEntry` produces the exact recursive ancestor chain `entryChain`.
-/
theorem iterateBackstackEntry_eq_entryChain (entry : BackstackEntry α) :
    (iterateBackstackEntry entry).toList = entryChain entry :=
  iterateBackstackEntry_eq_entryChain_Impl entry

/--
Theorem 2b: `iterateBackstackEntry` is always non-empty and starts with `entry` as its first element.
-/
theorem iterateBackstackEntry_nonempty_and_head (entry : BackstackEntry α) :
    (iterateBackstackEntry entry).size > 0 ∧
    (iterateBackstackEntry entry)[0]? = some entry :=
  iterateBackstackEntry_nonempty_and_head_Impl entry

/--
Theorem 2c: The last entry of `iterateBackstackEntryList` is always a root entry (`previous = none`).
-/
theorem iterateBackstackEntry_last_is_root (entry : BackstackEntry α) :
    ∃ root ∈ (iterateBackstackEntryList entry).getLast?, root.previous = none :=
  iterateBackstackEntry_last_is_root_Impl entry

/--
Theorem 3a: `previousEntryId` returns the `id` of `entry.previous` if present, or `none` if `entry` is a root.
-/
theorem previousEntryId_spec (entry : BackstackEntry α) :
    previousEntryId entry = entry.previous.map BackstackEntry.id :=
  previousEntryId_spec_Impl entry

/--
Theorem 3b: `canNavigateBack` is `true` if and only if `previousEntryId` is present (`isSome`).
-/
theorem canNavigateBack_iff (entry : BackstackEntry α) :
    canNavigateBack entry = (previousEntryId entry).isSome :=
  canNavigateBack_iff_Impl entry

/--
Theorem 3c: `isExpectedActor` allows execution if and only if `actorEntryId` is `none` or matches `currentEntryId`.
-/
theorem isExpectedActor_iff (currentEntryId : Uuid) (actorEntryId : Option Uuid) :
    isExpectedActor currentEntryId actorEntryId = true ↔
      (actorEntryId = none ∨ actorEntryId = some currentEntryId) :=
  isExpectedActor_iff_Impl currentEntryId actorEntryId

/--
Theorem 4: `initialBackstack` satisfies `ValidBackstackState` and `ValidTopologicalEntries`.
-/
theorem initialBackstack_valid (rootId : Uuid) (val : α) :
    ValidBackstackState (initialBackstack rootId val) ∧
    ValidTopologicalEntries (initialBackstack rootId val).entries.toList :=
  initialBackstack_valid_Impl rootId val

/--
Theorem 5a: `navigateWithFactory` to a fresh ID from a valid backstack state succeeds, preserves
`ValidBackstackState`, updates `currentEntryId` to `newId`, and links the new entry's `previous`
to the prior current entry.
-/
theorem navigateWithFactory_preserves_valid (state : BackstackState α)
    (valueFactory : BackstackEntry α → α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_fresh : findEntry state.entries newId = none) :
    ∃ state' cur,
      findEntry state.entries state.currentEntryId = some cur ∧
      navigateWithFactory state valueFactory newId = some state' ∧
      ValidBackstackState state' ∧
      state'.currentEntryId = newId ∧
      findEntry state'.entries newId = some (BackstackEntry.mkEntry (valueFactory cur) (some cur) newId) :=
  navigateWithFactory_preserves_valid_Impl state valueFactory newId h_valid h_fresh

/--
Theorem 5b: `navigateWithFactory` to a fresh ID preserves `ValidTopologicalEntries`.
-/
theorem navigateWithFactory_preserves_topological (state : BackstackState α)
    (valueFactory : BackstackEntry α → α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_top : ValidTopologicalEntries state.entries.toList)
    (h_fresh : findEntry state.entries newId = none)
    (h_nav : navigateWithFactory state valueFactory newId = some state') :
    ValidTopologicalEntries state'.entries.toList :=
  navigateWithFactory_preserves_topological_Impl state valueFactory newId h_valid h_top h_fresh h_nav

/--
Theorem 5c: `navigate` to a fresh ID from a valid backstack state succeeds, preserves
`ValidBackstackState` and `ValidTopologicalEntries`, and updates `currentEntryId` to `newId`.
-/
theorem navigate_preserves_valid (state : BackstackState α) (val : α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_top : ValidTopologicalEntries state.entries.toList)
    (h_fresh : findEntry state.entries newId = none) :
    ∃ state',
      navigate state val newId = some state' ∧
      ValidBackstackState state' ∧
      ValidTopologicalEntries state'.entries.toList ∧
      state'.currentEntryId = newId :=
  navigate_preserves_valid_Impl state val newId h_valid h_top h_fresh

/--
Theorem 6a: When the current entry is a root (`previous = none`), `popBackstack` fails (`returns none`).
-/
theorem popBackstack_root_fails (state : BackstackState α)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_root : cur.previous = none) :
    popBackstack state = none :=
  popBackstack_root_fails_Impl state h_cur h_root

/--
Theorem 6b: `popBackstack` from a valid backstack state preserves `ValidBackstackState` and evicts
the popped `currentEntryId` from `state'.entries`.
-/
theorem popBackstack_preserves_valid (state : BackstackState α)
    (h_valid : ValidBackstackState state)
    (h_pop : popBackstack state = some state') :
    ValidBackstackState state' ∧
    findEntry state'.entries state.currentEntryId = none :=
  popBackstack_preserves_valid_Impl state h_valid h_pop

/--
Theorem 6c: Popping immediately after `navigateWithFactory` to a fresh ID inverts the navigation
and recovers the exact original state.
-/
theorem pop_after_navigateWithFactory_eq_original (state : BackstackState α)
    (valueFactory : BackstackEntry α → α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_fresh : findEntry state.entries newId = none)
    (h_nav : navigateWithFactory state valueFactory newId = some state') :
    popBackstack state' = some state :=
  pop_after_navigateWithFactory_eq_original_Impl state valueFactory newId h_valid h_fresh h_nav

/--
Theorem 6d: Popping immediately after `navigate` to a fresh ID inverts the navigation
and recovers the exact original state.
-/
theorem pop_after_navigate_eq_original (state : BackstackState α) (val : α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_fresh : findEntry state.entries newId = none)
    (h_nav : navigate state val newId = some state') :
    popBackstack state' = some state :=
  pop_after_navigate_eq_original_Impl state val newId h_valid h_fresh h_nav

/--
Theorem 7a: `popUpTo` (both inclusive and non-inclusive) from a valid backstack state preserves
`ValidBackstackState` across arbitrary multi-step ancestor traversals.
-/
theorem popUpTo_preserves_valid (state : BackstackState α) (p : BackstackEntry α → Bool) (inclusive : Bool)
    (h_valid : ValidBackstackState state)
    (h_pop : popUpTo state p inclusive = some state') :
    ValidBackstackState state' :=
  popUpTo_preserves_valid_Impl state p inclusive h_valid h_pop

/--
Theorem 7b: Multi-step non-inclusive `popUpTo` soundness: if `popUpTo state p false = some state'`,
then `state'.currentEntryId` resolves to an ancestor `target ∈ iterateBackstackEntryList cur`
that satisfies `p target = true`.
-/
theorem popUpTo_non_inclusive_sound (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_pop : popUpTo state p false = some state') :
    ∃ target ∈ iterateBackstackEntryList cur,
      state'.currentEntryId = target.id ∧
      findEntry state'.entries target.id = some target ∧
      p target = true :=
  popUpTo_non_inclusive_sound_Impl state p h_valid h_cur h_pop

/--
Theorem 7c: Multi-step inclusive `popUpTo` soundness: if `popUpTo state p true = some state'`,
then there is an ancestor `matched ∈ iterateBackstackEntryList cur` satisfying `p matched = true`
whose parent `prev` (`matched.previous = some prev`) becomes the new current entry, and `matched`
itself is evicted from `state'.entries`.
-/
theorem popUpTo_inclusive_sound (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_pop : popUpTo state p true = some state') :
    ∃ matched ∈ iterateBackstackEntryList cur, ∃ prev,
      matched.previous = some prev ∧
      p matched = true ∧
      state'.currentEntryId = prev.id ∧
      findEntry state'.entries prev.id = some prev ∧
      findEntry state'.entries matched.id = none :=
  popUpTo_inclusive_sound_Impl state p h_valid h_cur h_pop

/--
Theorem 7d: Multi-step non-inclusive `popUpTo` completeness: if any ancestor in
`iterateBackstackEntryList cur` satisfies `p`, then `popUpTo state p false` succeeds (`isSome = true`).
-/
theorem popUpTo_complete_non_inclusive (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_exists : ∃ target ∈ iterateBackstackEntryList cur, p target = true) :
    (popUpTo state p false).isSome = true :=
  popUpTo_complete_non_inclusive_Impl state p h_cur h_exists

/--
Theorem 7e: Multi-step `popUpTo` failure completeness: if no ancestor in `iterateBackstackEntryList cur`
satisfies `p`, then `popUpTo state p inclusive` returns `none`.
-/
theorem popUpTo_none_when_no_match (state : BackstackState α) (p : BackstackEntry α → Bool) (inclusive : Bool)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_none : ∀ a ∈ iterateBackstackEntryList cur, p a = false) :
    popUpTo state p inclusive = none :=
  popUpTo_none_when_no_match_Impl state p inclusive h_cur h_none

/--
Theorem 7f: Non-inclusive `popUpTo` when `p` matches the current entry is the identity operation.
-/
theorem popUpTo_current_non_inclusive (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_match : p cur = true) :
    popUpTo state p false = some state :=
  popUpTo_current_non_inclusive_Impl state p h_valid h_cur h_match

/--
Theorem 7g: Inclusive `popUpTo` when `p` matches the current entry is identical to `popBackstack`.
-/
theorem popUpTo_current_inclusive_eq_pop (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_match : p cur = true) :
    popUpTo state p true = popBackstack state :=
  popUpTo_current_inclusive_eq_pop_Impl state p h_cur h_match

/--
Theorem 7h: Multi-step recurrence: when `p` does not match the current entry, `popUpTo` is equivalent
to executing `popBackstack` followed by `popUpTo` on the popped state.
-/
theorem popUpTo_step_when_not_matching (state : BackstackState α) (p : BackstackEntry α → Bool) (inclusive : Bool)
    (h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_no_match : p cur = false) :
    popUpTo state p inclusive = (popBackstack state).bind (fun prevState => popUpTo prevState p inclusive) :=
  popUpTo_step_when_not_matching_Impl state p inclusive h_valid h_cur h_no_match

/--
Theorem 7i: `popUpToId` specializes `popUpTo` to ID equality, preserves `ValidBackstackState`,
and on non-inclusive success transitions `currentEntryId` to `targetId` with `hasEntry state'.entries targetId = true`.
-/
theorem popUpToId_spec (state : BackstackState α) (targetId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_pop : popUpToId state targetId false = some state') :
    ValidBackstackState state' ∧
    state'.currentEntryId = targetId ∧
    hasEntry state'.entries targetId = true :=
  popUpToId_spec_Impl state targetId h_valid h_pop

/--
Theorem 7j: `popUpToValue` specializes `popUpTo` to value predicates, preserves `ValidBackstackState`,
and on non-inclusive success transitions to an entry whose value satisfies `p`.
-/
theorem popUpToValue_spec (state : BackstackState α) (p : α → Bool)
    (h_valid : ValidBackstackState state)
    (h_pop : popUpToValue state p false = some state') :
    ValidBackstackState state' ∧
    ∃ target, findEntry state'.entries state'.currentEntryId = some target ∧ p target.value = true :=
  popUpToValue_spec_Impl state p h_valid h_pop

/--
Theorem 8a: For ANY entry array `entries` and ANY `toSurrogate` function, `serializeBackstackEntries`
produces a surrogate array with pairwise distinct IDs (`allDistinctIds = true`) and valid topological
ordering (`isTopologicalOrder = true`).
-/
theorem serializeBackstackEntries_distinct_and_topological (entries : Array (BackstackEntry α))
    (toSurrogate : α → σ) :
    allDistinctIds (serializeBackstackEntries entries toSurrogate) = true ∧
    isTopologicalOrder (serializeBackstackEntries entries toSurrogate) = true :=
  serializeBackstackEntries_distinct_and_topological_Impl entries toSurrogate

/--
Theorem 8b: For ANY entry array `entries` and ANY `e ∈ entries.toList`, `serializeBackstackEntries`
includes the ID of `e` and of every ancestor `a ∈ iterateBackstackEntryList e` in the serialized output.
-/
theorem serializeBackstackEntries_contains_all (entries : Array (BackstackEntry α))
    (toSurrogate : α → σ) (e : BackstackEntry α) (he : e ∈ entries.toList) :
    ∀ a ∈ iterateBackstackEntryList e,
      hasSurrogateId (serializeBackstackEntries entries toSurrogate) a.id = true :=
  serializeBackstackEntries_contains_all_Impl entries toSurrogate e he

/--
Theorem 8c: Deserialization soundness: if `deserializeBackstackEntries` succeeds on `surrogates`,
then `surrogates` had pairwise distinct IDs and valid topological order, and the resulting `entries`
satisfy `allDistinctEntryIds` and `ValidTopologicalEntries`.
-/
theorem deserializeBackstackEntries_sound (surrogates : Array (BackstackEntrySurrogate σ))
    (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (h_deser : deserializeBackstackEntries surrogates fromSurrogate = some entries) :
    allDistinctIds surrogates = true ∧
    isTopologicalOrder surrogates = true ∧
    allDistinctEntryIds entries = true ∧
    ValidTopologicalEntries entries.toList :=
  deserializeBackstackEntries_sound_Impl surrogates fromSurrogate h_deser

/--
Theorem 8d: State deserialization soundness: if `deserializeBackstack` succeeds, the resulting
`BackstackState` is guaranteed to satisfy `ValidBackstackState` and `ValidTopologicalEntries`.
-/
theorem deserializeBackstack_preserves_valid (surrogates : Array (BackstackEntrySurrogate σ))
    (fromSurrogate : σ → Option (BackstackEntry α) → α) (currentId : Uuid)
    (h_deser : deserializeBackstack surrogates fromSurrogate currentId = some state) :
    ValidBackstackState state ∧
    ValidTopologicalEntries state.entries.toList :=
  deserializeBackstack_preserves_valid_Impl surrogates fromSurrogate currentId h_deser

/--
Theorem 8e: Universal entry serialization/deserialization round-trip: for any topologically valid
entry array `entries` and any surrogate conversion pair `(toSurrogate, fromSurrogate)` that round-trips
entry values given their parent entry, deserializing the serialized surrogates recovers `some entries`.
-/
theorem deserialize_serialize_entries_roundtrip (entries : Array (BackstackEntry α))
    (toSurrogate : α → σ) (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (h_top : ValidTopologicalEntries entries.toList)
    (h_val : ∀ e : BackstackEntry α, fromSurrogate (toSurrogate e.value) e.previous = e.value) :
    deserializeBackstackEntries (serializeBackstackEntries entries toSurrogate) fromSurrogate = some entries :=
  deserialize_serialize_entries_roundtrip_Impl entries toSurrogate fromSurrogate h_top h_val

/--
Theorem 8f: Universal backstack state serialization/deserialization round-trip: for any valid
topological `BackstackState` and any surrogate conversion pair `(toSurrogate, fromSurrogate)` that
round-trips entry values given their parent entry, `deserializeBackstack` of `serializeBackstack`
recovers `some state`.
-/
theorem deserialize_serialize_backstack_roundtrip (state : BackstackState α)
    (toSurrogate : α → σ) (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (h_valid : ValidBackstackState state)
    (h_top : ValidTopologicalEntries state.entries.toList)
    (h_val : ∀ e : BackstackEntry α, fromSurrogate (toSurrogate e.value) e.previous = e.value) :
    deserializeBackstack (serializeBackstack state toSurrogate) fromSurrogate state.currentEntryId = some state :=
  deserialize_serialize_backstack_roundtrip_Impl state toSurrogate fromSurrogate h_valid h_top h_val

end Navigation
