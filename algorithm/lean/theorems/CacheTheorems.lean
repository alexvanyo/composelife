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
import Algorithm.Cache
import proofs.CacheProofs

namespace Algorithm

/--
An empty cache contains zero entries.
-/
theorem cache_empty_size {α β : Type} [DecidableEq α] :
    (Cache.empty : Cache α β).size = 0 :=
  cache_empty_size_Impl

/--
Looking up any key in an empty cache returns none.
-/
theorem cache_lookup_empty {α β : Type} [DecidableEq α] (k : α) :
    (Cache.empty : Cache α β).lookup k = none :=
  cache_lookup_empty_Impl k

/--
An empty cache does not contain any key.
-/
theorem cache_contains_empty {α β : Type} [DecidableEq α] (k : α) :
    (Cache.empty : Cache α β).contains k = false :=
  cache_contains_empty_Impl k

/--
Calling `get` on an empty cache always returns the freshly loaded value.
-/
theorem cache_get_empty {α β : Type} [DecidableEq α]
    (load : α → β) (k : α) (gen : UInt64) :
    (Cache.empty.get load k gen).1 = load k :=
  cache_get_empty_Impl load k gen

/--
Memoization soundness on cache hit: if the cached value was sound, `get` returns `load k`.
-/
theorem cache_memoization_soundness_on_hit {α β : Type} [DecidableEq α]
    (c : Cache α β) (load : α → β) (k : α) (gen : UInt64) (v : β) (ts : UInt64)
    (hHit : c.lookup k = some (v, ts)) (hSound : v = load k) :
    (c.get load k gen).1 = load k :=
  cache_memoization_soundness_on_hit_Impl c load k gen v ts hHit hSound

/--
Memoization soundness on cache miss: `get` computes and returns `load k`.
-/
theorem cache_memoization_soundness_on_miss {α β : Type} [DecidableEq α]
    (c : Cache α β) (load : α → β) (k : α) (gen : UInt64)
    (hMiss : c.lookup k = none) :
    (c.get load k gen).1 = load k :=
  cache_memoization_soundness_on_miss_Impl c load k gen hMiss

/--
Pruning an empty cache yields an empty cache.
-/
theorem cache_prune_empty {α β : Type} [DecidableEq α] (oldestGen : UInt64) :
    (Cache.empty : Cache α β).prune oldestGen = Cache.empty :=
  cache_prune_empty_Impl oldestGen

end Algorithm
