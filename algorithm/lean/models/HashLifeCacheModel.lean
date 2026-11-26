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

namespace Algorithm.KotlinModel

/-- Standalone model of `Cache<K, V>` in `HashLifeCache.kt`. -/
structure CacheModel (K V : Type) [BEq K] where
  entries : List (K × V)
  lastAccessed : List (K × Int64)

def CacheModel.keysSynced {K V : Type} [BEq K] (c : CacheModel K V) : Prop :=
  c.entries.map Prod.fst = c.lastAccessed.map Prod.fst

def assocPut {K V : Type} [BEq K] (xs : List (K × V)) (k : K) (v : V) : List (K × V) :=
  if xs.any (fun p => p.1 == k) then
    xs.map (fun p => if p.1 == k then (k, v) else p)
  else
    xs ++ [(k, v)]

def CacheModel.put {K V : Type} [BEq K] (c : CacheModel K V) (k : K) (v : V) (gen : Int64) :
    CacheModel K V :=
  { entries := assocPut c.entries k v
    lastAccessed := assocPut c.lastAccessed k gen }

def CacheModel.prune {K V : Type} [BEq K] (c : CacheModel K V) (oldestGen : Int64) :
    CacheModel K V :=
  let keptKeys := (c.lastAccessed.filter (fun p => !(p.2 < oldestGen))).map Prod.fst
  { entries := c.entries.filter (fun p => keptKeys.contains p.1)
    lastAccessed := c.lastAccessed.filter (fun p => !(p.2 < oldestGen)) }

/-- Standalone model of `Equivalence.Wrapper.equals` (same equivalence identity + `isEquivalent`). -/
def wrapperEqualsModel {T : Type} (eqId1 eqId2 : Nat) (isEq : T → T → Bool) (v1 v2 : T) : Bool :=
  eqId1 == eqId2 && isEq v1 v2

end Algorithm.KotlinModel
