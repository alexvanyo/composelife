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

namespace Navigation

/--
Pure recursive specification of the ancestor chain of a `BackstackEntry` from the entry to the root.
-/
def entryChain : BackstackEntry α → List (BackstackEntry α)
  | .mk v none i => [.mk v none i]
  | .mk v (some prev) i => (.mk v (some prev) i) :: entryChain prev

/--
Helper checking whether a list of IDs contains duplicates.
-/
def hasDuplicateId (ids : List Uuid) : Bool :=
  match ids with
  | [] => false
  | x :: xs => xs.contains x || hasDuplicateId xs

/--
Check if all IDs in a surrogate array are pairwise distinct.
-/
def allDistinctIds (surrogates : Array (BackstackEntrySurrogate σ)) : Bool :=
  !hasDuplicateId (surrogates.toList.map (·.id))

/--
Check if all IDs in an entry array are pairwise distinct.
-/
def allDistinctEntryIds (entries : Array (BackstackEntry α)) : Bool :=
  !hasDuplicateId (entries.toList.map BackstackEntry.id)

/--
Helper checking whether a list of surrogates satisfies topological dependency order (parents before children).
-/
def isTopologicalOrderList (seen : List Uuid) (entries : List (BackstackEntrySurrogate σ)) : Bool :=
  match entries with
  | [] => true
  | e :: rest =>
    match e.previousId with
    | none => isTopologicalOrderList (e.id :: seen) rest
    | some pid => seen.contains pid && isTopologicalOrderList (e.id :: seen) rest

/--
Validate whether a sequence of surrogates is in topological dependency order (parents before children).
-/
def isTopologicalOrder (surrogates : Array (BackstackEntrySurrogate σ)) : Bool :=
  isTopologicalOrderList [] surrogates.toList

/--
Check if a surrogate with `targetId` exists in `surrogates`.
-/
def hasSurrogateId (surrogates : Array (BackstackEntrySurrogate σ)) (targetId : Uuid) : Bool :=
  hasSurrogateIdList surrogates.toList targetId

/--
Converts a single `BackstackEntry` to its `BackstackEntrySurrogate` using `toSurrogate`.
-/
def entryToSurrogate (toSurrogate : α → σ) (e : BackstackEntry α) : BackstackEntrySurrogate σ :=
  ⟨e.id, previousEntryId e, toSurrogate e.value⟩

/--
A valid backstack state satisfies:
1. All entry IDs in `state.entries` are pairwise distinct.
2. `state.currentEntryId` resolves to an entry `current` in `state.entries`.
3. Every ancestor `a` in the active chain `iterateBackstackEntryList current` is present in `state.entries` at `a.id`.
-/
def ValidBackstackState (state : BackstackState α) : Prop :=
  allDistinctEntryIds state.entries = true ∧
  ∃ current,
    findEntry state.entries state.currentEntryId = some current ∧
    ∀ a ∈ iterateBackstackEntryList current, findEntry state.entries a.id = some a

/--
A list of entries `entries` is topologically ordered after prefix `seen` when:
each entry `e` has a fresh ID not in `seen`, and if `e.previous = some prev`,
`prev` is already present in `seen` at `prev.id`.
-/
def ValidTopologicalEntriesAfter (seen : List (BackstackEntry α)) : List (BackstackEntry α) → Prop
  | [] => True
  | e :: rest =>
    findEntryList seen e.id = none ∧
    (∀ prev, e.previous = some prev → findEntryList seen prev.id = some prev) ∧
    ValidTopologicalEntriesAfter (seen ++ [e]) rest

/--
A list of entries is a valid topologically ordered entry list starting from an empty prefix.
-/
def ValidTopologicalEntries (entries : List (BackstackEntry α)) : Prop :=
  ValidTopologicalEntriesAfter [] entries

end Navigation
