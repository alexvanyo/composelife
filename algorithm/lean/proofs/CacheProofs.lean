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

namespace Algorithm

theorem cache_empty_size_Impl {α β : Type} [DecidableEq α] :
    (Cache.empty : Cache α β).size = 0 := by
  rfl

theorem cache_lookup_empty_Impl {α β : Type} [DecidableEq α] (k : α) :
    (Cache.empty : Cache α β).lookup k = none := by
  rfl

theorem cache_contains_empty_Impl {α β : Type} [DecidableEq α] (k : α) :
    (Cache.empty : Cache α β).contains k = false := by
  rfl

theorem cache_get_empty_Impl {α β : Type} [DecidableEq α]
    (load : α → β) (k : α) (gen : UInt64) :
    (Cache.empty.get load k gen).1 = load k := by
  rfl

theorem cache_memoization_soundness_on_hit_Impl {α β : Type} [DecidableEq α]
    (c : Cache α β) (load : α → β) (k : α) (gen : UInt64) (v : β) (ts : UInt64)
    (hHit : c.lookup k = some (v, ts)) (hSound : v = load k) :
    (c.get load k gen).1 = load k := by
  dsimp [Cache.get]
  rw [hHit]
  exact hSound

theorem cache_memoization_soundness_on_miss_Impl {α β : Type} [DecidableEq α]
    (c : Cache α β) (load : α → β) (k : α) (gen : UInt64)
    (hMiss : c.lookup k = none) :
    (c.get load k gen).1 = load k := by
  dsimp [Cache.get]
  rw [hMiss]

theorem cache_prune_empty_Impl {α β : Type} [DecidableEq α] (oldestGen : UInt64) :
    (Cache.empty : Cache α β).prune oldestGen = Cache.empty := by
  rfl

end Algorithm
