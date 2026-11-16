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

namespace Navigation.Model

/-- Unique identifier for a backstack entry (models `kotlin.uuid.Uuid`). -/
abbrev EntryId := Nat

/-- Inductive model of `com.alexvanyo.composelife.navigation.BackstackEntry<T>`.
    Every value is structurally finite and acyclic, rooted at `.root`. -/
inductive BackstackEntry (α : Type) where
  | root (value : α) (id : EntryId)
  | node (value : α) (previous : BackstackEntry α) (id : EntryId)
  deriving DecidableEq, Repr, Inhabited

/-- Smart constructor matching `BackstackEntry(value, previous, id)` in Kotlin. -/
def BackstackEntry.mk {α : Type} (value : α) (previous : Option (BackstackEntry α)) (id : EntryId) :
    BackstackEntry α :=
  match previous with
  | none => .root value id
  | some prev => .node value prev id

def BackstackEntry.value {α : Type} : BackstackEntry α → α
  | .root v _ => v
  | .node v _ _ => v

def BackstackEntry.previous {α : Type} : BackstackEntry α → Option (BackstackEntry α)
  | .root _ _ => none
  | .node _ p _ => some p

def BackstackEntry.id {α : Type} : BackstackEntry α → EntryId
  | .root _ i => i
  | .node _ _ i => i

/-- Number of entries in the `previous`-pointer chain rooted at `none` (`≥ 1`). -/
def BackstackEntry.depth {α : Type} : BackstackEntry α → Nat
  | .root _ _ => 1
  | .node _ prev _ => 1 + prev.depth

/-- Finite `previous`-pointer chain from head down to the root entry. -/
def BackstackEntry.toChain {α : Type} : BackstackEntry α → List (BackstackEntry α)
  | e@(.root _ _) => [e]
  | e@(.node _ prev _) => e :: prev.toChain

/-- Associative list model of `MutableBackstackMap<T>` (`MutableMap<Uuid, BackstackEntry<T>>`). -/
abbrev BackstackMap (α : Type) := List (EntryId × BackstackEntry α)

def mapLookup {α : Type} (m : BackstackMap α) (k : EntryId) : Option (BackstackEntry α) :=
  (m.find? (fun p => p.1 == k)).map Prod.snd

def mapPut {α : Type} (m : BackstackMap α) (k : EntryId) (v : BackstackEntry α) : BackstackMap α :=
  (k, v) :: m.filter (fun p => p.1 != k)

def mapRemove {α : Type} (m : BackstackMap α) (k : EntryId) : BackstackMap α :=
  m.filter (fun p => p.1 != k)

def mapContains {α : Type} (m : BackstackMap α) (k : EntryId) : Bool :=
  (mapLookup m k).isSome

def mapKeys {α : Type} (m : BackstackMap α) : List EntryId :=
  m.map Prod.fst

/-- Well-formedness invariant for `(map, currentEntryId)`:
    no duplicate keys, `currentEntryId` resolves in `map`, and `map` binds precisely
    the finite `previous`-pointer chain of the head entry with consistent `id`s. -/
structure WellFormedBackstack {α : Type} (m : BackstackMap α) (currentEntryId : EntryId) : Prop where
  noDupKeys : (mapKeys m).Nodup
  headSome : ∃ head, mapLookup m currentEntryId = some head
  chainMatchesMap : ∀ head, mapLookup m currentEntryId = some head →
    ∀ k e, mapLookup m k = some e ↔ (e ∈ head.toChain ∧ e.id = k)

/-- Failure modes matching Kotlin exceptions in `BackstackNavigation.kt`. -/
inductive NavError where
  | missingEntry
  | popLastEntry
  | predicateNotFound
  deriving DecidableEq, Repr, Inhabited

/-- Result of executing a backstack navigation operation. -/
inductive NavResult (α : Type) where
  | ok (map : BackstackMap α) (currentEntryId : EntryId)
  | error (err : NavError)
  deriving DecidableEq, Repr, Inhabited

/-- Model of `MutableBackstackMap<T>.navigate(currentEntryId, valueFactory, id)`. -/
def navigateModel {α : Type} (m : BackstackMap α) (currentEntryId : EntryId)
    (valueFactory : BackstackEntry α → α) (id : EntryId) : NavResult α :=
  match mapLookup m currentEntryId with
  | none => .error .missingEntry
  | some prev =>
    let cur : BackstackEntry α := .node (valueFactory prev) prev id
    .ok (mapPut m id cur) id

/-- Model of `MutableBackstackMap<T>.navigate(currentEntryId, value, id)`. -/
def navigateValueModel {α : Type} (m : BackstackMap α) (currentEntryId : EntryId)
    (value : α) (id : EntryId) : NavResult α :=
  navigateModel m currentEntryId (fun _ => value) id

/-- Model of `MutableBackstackMap<T>.popBackstack(currentEntryId)`. -/
def popBackstackModel {α : Type} (m : BackstackMap α) (currentEntryId : EntryId) : NavResult α :=
  match mapLookup m currentEntryId with
  | none => .error .missingEntry
  | some cur =>
    match cur.previous with
    | none => .error .popLastEntry
    | some prev => .ok (mapRemove m cur.id) prev.id

/-- Structural loop model for `popUpTo`'s `while (!entryPredicate(current))` loop. -/
def popUpToWalk {α : Type} (entryPredicate : BackstackEntry α → Bool)
    (m : BackstackMap α) : BackstackEntry α → Option (BackstackMap α × BackstackEntry α)
  | cur@(.root _ _) =>
    if entryPredicate cur then some (m, cur) else none
  | cur@(.node _ prev id) =>
    if entryPredicate cur then some (m, cur)
    else popUpToWalk entryPredicate (mapRemove m id) prev

/-- Fuel-bounded step model of `popUpToWalk` showing exact loop iteration count. -/
def popUpToWalkFuel {α : Type} (entryPredicate : BackstackEntry α → Bool) :
    Nat → BackstackMap α → BackstackEntry α → Option (BackstackMap α × BackstackEntry α)
  | 0, m, cur => if entryPredicate cur then some (m, cur) else none
  | n + 1, m, cur =>
    if entryPredicate cur then some (m, cur)
    else
      match cur with
      | .root _ _ => none
      | .node _ prev id => popUpToWalkFuel entryPredicate n (mapRemove m id) prev

/-- Distance (number of loop steps) from `cur` to the first ancestor matching `entryPredicate`. -/
def matchDistance? {α : Type} (entryPredicate : BackstackEntry α → Bool) :
    BackstackEntry α → Option Nat
  | cur@(.root _ _) => if entryPredicate cur then some 0 else none
  | cur@(.node _ prev _) =>
    if entryPredicate cur then some 0
    else (matchDistance? entryPredicate prev).map (· + 1)

/-- Model of `MutableBackstackMap<T>.popUpTo(currentEntryId, entryPredicate, inclusive)`. -/
def popUpToModel {α : Type} (m : BackstackMap α) (currentEntryId : EntryId)
    (entryPredicate : BackstackEntry α → Bool) (inclusive : Bool := false) : NavResult α :=
  match mapLookup m currentEntryId with
  | none => .error .missingEntry
  | some head =>
    match popUpToWalk entryPredicate m head with
    | none => .error .predicateNotFound
    | some (m1, target) =>
      if inclusive then
        let m2 := mapRemove m1 target.id
        match target.previous with
        | none => .error .popLastEntry
        | some prev => .ok m2 prev.id
      else
        .ok m1 target.id

/-- Model of `MutableBackstackMap<T>.popUpTo(currentEntryId, id, inclusive)`. -/
def popUpToIdModel {α : Type} (m : BackstackMap α) (currentEntryId : EntryId)
    (id : EntryId) (inclusive : Bool := false) : NavResult α :=
  popUpToModel m currentEntryId (fun e => e.id == id) inclusive

/-- Model of `MutableBackstackMap<T>.popUpToValue(currentEntryId, predicate, inclusive)`. -/
def popUpToValueModel {α : Type} (m : BackstackMap α) (currentEntryId : EntryId)
    (predicate : α → Bool) (inclusive : Bool := false) : NavResult α :=
  popUpToModel m currentEntryId (fun e => predicate e.value) inclusive

end Navigation.Model
