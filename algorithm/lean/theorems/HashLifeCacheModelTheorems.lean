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

import models.HashLifeCacheModel
import proofs.HashLifeCacheModelProofs

namespace Algorithm.KotlinModel

theorem cacheModel_put_preserves_keysSynced {K V : Type} [BEq K] [LawfulBEq K]
    (c : CacheModel K V) (k : K) (v : V) (gen : Int64)
    (hsync : c.keysSynced) :
    (c.put k v gen).keysSynced :=
  cacheModel_put_preserves_keysSynced_Impl c k v gen hsync

theorem cacheModel_prune_retains_recent {K V : Type} [BEq K]
    (c : CacheModel K V) (oldestGen : Int64) :
    ∀ p ∈ (c.prune oldestGen).lastAccessed, ¬ (p.2 < oldestGen) :=
  cacheModel_prune_retains_recent_Impl c oldestGen

theorem wrapperEqualsModel_refl {T : Type} (eqId : Nat) (isEq : T → T → Bool)
    (hrefl : ∀ x, isEq x x = true) (v : T) :
    wrapperEqualsModel eqId eqId isEq v v = true :=
  wrapperEqualsModel_refl_Impl eqId isEq hrefl v

theorem wrapperEqualsModel_symm {T : Type} (eqId1 eqId2 : Nat) (isEq : T → T → Bool)
    (hsymm : ∀ x y, isEq x y = isEq y x) (v1 v2 : T) :
    wrapperEqualsModel eqId1 eqId2 isEq v1 v2 = wrapperEqualsModel eqId2 eqId1 isEq v2 v1 :=
  wrapperEqualsModel_symm_Impl eqId1 eqId2 isEq hsymm v1 v2

end Algorithm.KotlinModel
