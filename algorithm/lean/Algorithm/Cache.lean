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

import Algorithm.Basic

namespace Algorithm

/--
A cache entry storing a key-value mapping along with the generation timestamp
of when it was last accessed, mirroring HashLifeAlgorithm.kt's Cache.
-/
structure CacheEntry (α : Type) (β : Type) where
  key : α
  val : β
  lastAccessed : UInt64
deriving DecidableEq

/--
A generational LRU / memoization cache model mirroring Cache<K, V> in HashLifeAlgorithm.kt.
Stores entries associated with the generation at which they were accessed.
-/
structure Cache (α : Type) (β : Type) where
  entries : List (CacheEntry α β)
deriving DecidableEq

/--
Creates an empty Cache.
-/
def Cache.empty {α β : Type} [DecidableEq α] : Cache α β :=
  { entries := [] }

/--
Looks up an entry by key in the cache.
-/
def Cache.lookup {α β : Type} [DecidableEq α] (c : Cache α β) (k : α) : Option (β × UInt64) :=
  match c.entries.find? (fun e => e.key == k) with
  | some e => some (e.val, e.lastAccessed)
  | none => none

/--
Checks whether a key is present in the cache.
-/
def Cache.contains {α β : Type} [DecidableEq α] (c : Cache α β) (k : α) : Bool :=
  (c.lookup k).isSome

/--
Number of cached elements.
-/
def Cache.size {α β : Type} [DecidableEq α] (c : Cache α β) : Nat :=
  c.entries.length

/--
Inserts or updates an entry in the cache with the given access generation.
-/
def Cache.insert {α β : Type} [DecidableEq α] (c : Cache α β) (k : α) (v : β) (gen : UInt64) : Cache α β :=
  let remaining := c.entries.filter (fun e => !(e.key == k))
  { entries := { key := k, val := v, lastAccessed := gen } :: remaining }

/--
Retrieves the value for key `k` from the cache.
If present, updates the `lastAccessed` generation index.
If absent, computes the value via `load`, inserts it into the cache, and updates `lastAccessed`.
Matches `Cache.get` in HashLifeAlgorithm.kt.
-/
def Cache.get {α β : Type} [DecidableEq α]
    (c : Cache α β) (load : α → β) (k : α) (currentGen : UInt64) : β × Cache α β :=
  match c.lookup k with
  | some (v, _) =>
    (v, c.insert k v currentGen)
  | none =>
    let v := load k
    (v, c.insert k v currentGen)

/--
Prunes the cache by removing all entries whose `lastAccessed` generation index
is strictly less than `oldestGenerationToKeep`.
Matches `Cache.prune` in HashLifeAlgorithm.kt.
-/
def Cache.prune {α β : Type} [DecidableEq α] (c : Cache α β) (oldestGenerationToKeep : UInt64) : Cache α β :=
  { entries := c.entries.filter (fun e => !(e.lastAccessed < oldestGenerationToKeep)) }

/--
Specialized ObjectLongCache where values are 64-bit integers (LeafNodes).
Matches ObjectLongCache<K> in HashLifeAlgorithm.kt.
-/
abbrev ObjectLongCache (α : Type) [DecidableEq α] := Cache α UInt64

/--
Specialized LongIntCache where keys are 64-bit integers and values are 32-bit integers.
Matches LongIntCache in HashLifeAlgorithm.kt.
-/
abbrev LongIntCache := Cache UInt64 UInt32

end Algorithm
