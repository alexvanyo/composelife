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

import Lean.Compiler.Kotlin
open Lean.Compiler.Kotlin

namespace Navigation

/--
A 128-bit UUID representation matching RFC 4122 / RFC 9562 and Kotlin's `kotlin.uuid.Uuid`.
Represented as two 64-bit unsigned integers: `mostSignificantBits` and `leastSignificantBits`.
-/
@[extern "kotlin:kotlin.uuid.Uuid"]
structure Uuid where
  mostSignificantBits : UInt64
  leastSignificantBits : UInt64
deriving DecidableEq, Repr, Inhabited

attribute [kotlin_expr "({0} == {1})"] instDecidableEqUuid

/--
An entry in the backstack, corresponding directly to Kotlin's `BackstackEntry<T>`.
Each entry holds a `value`, an optional link to its `previous` entry in the chain, and a unique `id`.
-/
@[extern "kotlin:kotlin.Any"]
inductive BackstackEntry (α : Type u) where
  | mk (value : α) (previous : Option (BackstackEntry α)) (id : Uuid) : BackstackEntry α

/--
Constructs a `BackstackEntry` instance.
-/
@[noinline]
def BackstackEntry.mkEntry (value : α) (previous : Option (BackstackEntry α)) (id : Uuid) : BackstackEntry α :=
  .mk value previous id
attribute [kotlin_expr "BackstackEntry<Any?>({0}, ({1} as com.alexvanyo.composelife.navigation.BackstackEntry<Any?>?), {2})"] BackstackEntry.mkEntry

/--
The destination value stored in this `BackstackEntry`.
-/
@[noinline]
def BackstackEntry.value : BackstackEntry α → α
  | .mk v _ _ => v
attribute [kotlin_expr "({0} as com.alexvanyo.composelife.navigation.BackstackEntry<*>).value"] BackstackEntry.value

/--
The previous `BackstackEntry` in the backstack chain, or `none` if this is a root entry.
-/
@[noinline]
def BackstackEntry.previous : BackstackEntry α → Option (BackstackEntry α)
  | .mk _ p _ => p
attribute [kotlin_expr "({0} as com.alexvanyo.composelife.navigation.BackstackEntry<*>).previous"] BackstackEntry.previous

/--
The unique identifier of this `BackstackEntry`.
-/
@[noinline]
def BackstackEntry.id : BackstackEntry α → Uuid
  | .mk _ _ i => i
attribute [kotlin_expr "({0} as com.alexvanyo.composelife.navigation.BackstackEntry<*>).id"] BackstackEntry.id

/--
A flat serializable surrogate representation of a single backstack entry, corresponding to Kotlin's
`BackstackEntrySurrogate<S>`.
-/
@[kotlin_class "data class BackstackEntrySurrogate"]
structure BackstackEntrySurrogate (σ : Type u) where
  id : Uuid
  previousId : Option Uuid
  surrogate : σ
deriving DecidableEq, Repr, Inhabited

/--
An immutable backstack model representing a collection of backstack entries and a current entry pointer.
-/
@[kotlin_class "data class BackstackModel"]
structure BackstackState (α : Type u) where
  entries : Array (BackstackEntry α)
  currentEntryId : Uuid

/--
Walks the `previous` chain from `cur` to the root entry, returning the list of entries in order from `cur` to root.
-/
def iterateBackstackEntryList (cur : BackstackEntry α) : List (BackstackEntry α) :=
  match _h : cur.previous with
  | none => [cur]
  | some prev => cur :: iterateBackstackEntryList prev
termination_by sizeOf cur
decreasing_by
  cases cur with
  | mk v p i =>
    dsimp [BackstackEntry.previous] at _h
    subst _h
    decreasing_tactic

/--
Walks the `previous` chain from `entry` to the root entry, returning an array of entries for iteration.
-/
@[export navigation_iterate_backstack_entry]
def iterateBackstackEntry (entry : BackstackEntry α) : Array (BackstackEntry α) :=
  (iterateBackstackEntryList entry).toArray

/--
Returns the `id` of the previous entry in the backstack chain, if any.
-/
@[export navigation_previous_entry_id]
def previousEntryId (currentEntry : BackstackEntry α) : Option Uuid :=
  match currentEntry.previous with
  | none => none
  | some prev => some prev.id

/--
Returns `true` if `popBackstack` is possible from `currentEntry` (i.e., `currentEntry.previous` is present).
-/
@[export navigation_can_navigate_back]
def canNavigateBack (currentEntry : BackstackEntry α) : Bool :=
  currentEntry.previous.isSome

/--
Guards whether a navigation action from `actorEntryId` should be executed when the current entry is `currentEntryId`.
-/
@[export navigation_is_expected_actor]
def isExpectedActor (currentEntryId : Uuid) (actorEntryId : Option Uuid) : Bool :=
  match actorEntryId with
  | none => true
  | some actorId => actorId == currentEntryId

/--
Look up an entry by `targetId` in a list of entries.
-/
def findEntryList (entries : List (BackstackEntry α)) (targetId : Uuid) : Option (BackstackEntry α) :=
  entries.find? (fun e => e.id == targetId)

/--
Look up an entry by `targetId` in an array of entries.
-/
def findEntry (entries : Array (BackstackEntry α)) (targetId : Uuid) : Option (BackstackEntry α) :=
  findEntryList entries.toList targetId

/--
Check if an entry with `targetId` exists in `entries`.
-/
def hasEntry (entries : Array (BackstackEntry α)) (targetId : Uuid) : Bool :=
  (findEntry entries targetId).isSome

/--
Remove all entries with `targetId` from a list of entries.
-/
def removeEntryList (entries : List (BackstackEntry α)) (targetId : Uuid) : List (BackstackEntry α) :=
  entries.filter (fun e => e.id != targetId)

/--
Remove all entries with `targetId` from an array of entries.
-/
def removeEntry (entries : Array (BackstackEntry α)) (targetId : Uuid) : Array (BackstackEntry α) :=
  (removeEntryList entries.toList targetId).toArray

/--
Create an initial single-entry backstack state with the given root entry `rootId` and value `val`.
-/
@[export navigation_initial_backstack]
def initialBackstack (rootId : Uuid) (val : α) : BackstackState α :=
  { entries := #[BackstackEntry.mkEntry val none rootId], currentEntryId := rootId }

/--
Navigate to a new destination created by `valueFactory` from the current entry, with identifier `newId`.
Returns `none` if `state.currentEntryId` does not exist in `state.entries`.
-/
@[export navigation_navigate_with_factory]
def navigateWithFactory (state : BackstackState α) (valueFactory : BackstackEntry α → α) (newId : Uuid) :
    Option (BackstackState α) :=
  match findEntry state.entries state.currentEntryId with
  | none => none
  | some previous =>
    let newEntry := BackstackEntry.mkEntry (valueFactory previous) (some previous) newId
    let entriesWithoutNewId := removeEntry state.entries newId
    some { entries := entriesWithoutNewId.push newEntry, currentEntryId := newId }

/--
Navigate to a new destination with constant value `newVal` and identifier `newId`.
-/
@[export navigation_navigate]
def navigate (state : BackstackState α) (newVal : α) (newId : Uuid) : Option (BackstackState α) :=
  navigateWithFactory state (fun _ => newVal) newId

/--
Pop the current entry from the backstack, transitioning to its `previous` entry.
Returns `none` if the current entry does not exist or has no `previous` entry (root entry).
-/
@[export navigation_pop_backstack]
def popBackstack (state : BackstackState α) : Option (BackstackState α) :=
  match findEntry state.entries state.currentEntryId with
  | none => none
  | some cur =>
    match cur.previous with
    | none => none
    | some prev =>
      some { entries := removeEntry state.entries cur.id, currentEntryId := prev.id }

/--
Walks the `previous` chain starting at `current`, removing non-matching entries until `entryPredicate`
is satisfied. If `inclusive` is `true`, also removes the matching entry and transitions to its `previous` entry.
-/
def popUpToWalk (entries : Array (BackstackEntry α)) (current : BackstackEntry α)
    (entryPredicate : BackstackEntry α → Bool) (inclusive : Bool) : Option (BackstackState α) :=
  if entryPredicate current then
    if inclusive then
      match current.previous with
      | none => none
      | some prev => some { entries := removeEntry entries current.id, currentEntryId := prev.id }
    else
      some { entries := entries, currentEntryId := current.id }
  else
    let entries' := removeEntry entries current.id
    match _h : current.previous with
    | none => none
    | some prev => popUpToWalk entries' prev entryPredicate inclusive
termination_by sizeOf current
decreasing_by
  cases current with
  | mk v p i =>
    dsimp [BackstackEntry.previous] at _h
    subst _h
    decreasing_tactic

/--
Pop the backstack up to the first ancestor entry satisfying `entryPredicate`.
If `inclusive` is `true`, also pops the matching entry.
Returns `none` if no entry in the chain matches or if an inclusive pop attempts to pop the root entry.
-/
@[export navigation_pop_up_to]
def popUpTo (state : BackstackState α) (entryPredicate : BackstackEntry α → Bool) (inclusive : Bool) :
    Option (BackstackState α) :=
  match findEntry state.entries state.currentEntryId with
  | none => none
  | some current => popUpToWalk state.entries current entryPredicate inclusive

/--
Pop the backstack up to the entry with identifier `targetId`.
-/
@[export navigation_pop_up_to_id]
def popUpToId (state : BackstackState α) (targetId : Uuid) (inclusive : Bool) : Option (BackstackState α) :=
  popUpTo state (fun e => e.id == targetId) inclusive

/--
Pop the backstack up to the first entry whose value satisfies `predicate`.
-/
@[export navigation_pop_up_to_value]
def popUpToValue (state : BackstackState α) (predicate : α → Bool) (inclusive : Bool) : Option (BackstackState α) :=
  popUpTo state (fun e => predicate e.value) inclusive

/--
Check if a surrogate with `targetId` is already present in `surrogates`.
-/
def hasSurrogateIdList (surrogates : List (BackstackEntrySurrogate σ)) (targetId : Uuid) : Bool :=
  (surrogates.find? (fun s => s.id == targetId)).isSome

/--
Topologically serialize `entry` and its ancestor chain into `acc`, ensuring parent surrogates
are emitted before their children and avoiding duplicate IDs.
-/
def serializeEntryChainList (toSurrogate : α → σ) (entry : BackstackEntry α)
    (acc : List (BackstackEntrySurrogate σ)) : List (BackstackEntrySurrogate σ) :=
  let accAfterPrev :=
    match _h : entry.previous with
    | none => acc
    | some prev => serializeEntryChainList toSurrogate prev acc
  if hasSurrogateIdList accAfterPrev entry.id then
    accAfterPrev
  else
    accAfterPrev ++ [⟨entry.id, previousEntryId entry, toSurrogate entry.value⟩]
termination_by sizeOf entry
decreasing_by
  cases entry with
  | mk v p i =>
    dsimp [BackstackEntry.previous] at _h
    subst _h
    decreasing_tactic

/--
Topologically serialize a list of entries into `acc`.
-/
def serializeEntriesList (toSurrogate : α → σ) (entries : List (BackstackEntry α))
    (acc : List (BackstackEntrySurrogate σ)) : List (BackstackEntrySurrogate σ) :=
  match entries with
  | [] => acc
  | e :: rest => serializeEntriesList toSurrogate rest (serializeEntryChainList toSurrogate e acc)

/--
Topologically serialize an array of `BackstackEntry` into an array of `BackstackEntrySurrogate`.
-/
@[export navigation_serialize_backstack_entries]
def serializeBackstackEntries (entries : Array (BackstackEntry α)) (toSurrogate : α → σ) :
    Array (BackstackEntrySurrogate σ) :=
  (serializeEntriesList toSurrogate entries.toList []).toArray

/--
Deserialize a topologically ordered list of `BackstackEntrySurrogate` into a list of `BackstackEntry`,
reconstructing each entry's `previous` pointer and value via `fromSurrogate`.
Returns `none` if duplicate IDs are encountered or if a `previousId` references an entry not yet deserialized.
-/
def deserializeEntriesList (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (surrogates : List (BackstackEntrySurrogate σ))
    (acc : List (BackstackEntry α)) : Option (List (BackstackEntry α)) :=
  match surrogates with
  | [] => some acc
  | s :: rest =>
    if (findEntryList acc s.id).isSome then
      none
    else
      match s.previousId with
      | none =>
        let val := fromSurrogate s.surrogate none
        let entry := BackstackEntry.mkEntry val none s.id
        deserializeEntriesList fromSurrogate rest (acc ++ [entry])
      | some pid =>
        match findEntryList acc pid with
        | none => none
        | some prev =>
          let val := fromSurrogate s.surrogate (some prev)
          let entry := BackstackEntry.mkEntry val (some prev) s.id
          deserializeEntriesList fromSurrogate rest (acc ++ [entry])

/--
Deserialize an array of `BackstackEntrySurrogate` into an array of `BackstackEntry`.
-/
@[export navigation_deserialize_backstack_entries]
def deserializeBackstackEntries (surrogates : Array (BackstackEntrySurrogate σ))
    (fromSurrogate : σ → Option (BackstackEntry α) → α) : Option (Array (BackstackEntry α)) :=
  match deserializeEntriesList fromSurrogate surrogates.toList [] with
  | none => none
  | some list => some list.toArray

/--
Serialize a `BackstackState` into a topologically ordered array of `BackstackEntrySurrogate`.
-/
@[export navigation_serialize_backstack]
def serializeBackstack (state : BackstackState α) (toSurrogate : α → σ) :
    Array (BackstackEntrySurrogate σ) :=
  serializeBackstackEntries state.entries toSurrogate

/--
Deserialize an array of `BackstackEntrySurrogate` and a `currentId` into a `BackstackState`.
Returns `none` if the surrogates fail validation or if `currentId` is not present among the entries.
-/
@[export navigation_deserialize_backstack]
def deserializeBackstack (surrogates : Array (BackstackEntrySurrogate σ))
    (fromSurrogate : σ → Option (BackstackEntry α) → α) (currentId : Uuid) :
    Option (BackstackState α) :=
  match deserializeBackstackEntries surrogates fromSurrogate with
  | none => none
  | some entries =>
    if hasEntry entries currentId then
      some { entries := entries, currentEntryId := currentId }
    else
      none

@[kotlin_file]
def backstackFileSpec : FileSpec := {
  imports := #[
    "import kotlinx.serialization.Serializable",
    "import kotlin.uuid.Uuid"
  ]
  items := #[
    .cls {
      name := "BackstackEntrySurrogate"
      header := "@Serializable\ninternal data class BackstackEntrySurrogate<S>(val id: Uuid, val previousId: Uuid?, val surrogate: S)"
      body := #[
        .verbatim "companion object {}",
        .members
      ]
    },
    .topLevel
  ]
}

end Navigation
