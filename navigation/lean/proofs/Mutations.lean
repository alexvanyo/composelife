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

import models.BackstackNavigationModel
import proofs.BackstackNavigationModelProofs

namespace Navigation.Mutations

open Navigation.Model

/-- Non-vacuity check: a concrete two-entry backstack satisfies `WellFormedBackstack`
    and demonstrates `navigate`, `popBackstack`, and `popUpTo` behavior. -/
theorem wellFormed_concrete_nonvacuous :
    let e1 : BackstackEntry String := .root "home" 1
    let e2 : BackstackEntry String := .node "settings" e1 2
    let m : BackstackMap String := [(2, e2), (1, e1)]
    WellFormedBackstack m 2 ∧
    mapLookup m 3 = none ∧
    popBackstackModel m 2 = .ok [(1, e1)] 1 ∧
    popUpToIdModel m 2 1 false = .ok [(1, e1)] 1 := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · decide
  · exact ⟨.node "settings" (.root "home" 1) 2, rfl⟩
  · intro head hhead k e
    have hEq : head = .node "settings" (.root "home" 1) 2 := Option.some.inj hhead.symm
    subst hEq
    constructor
    · intro hl
      by_cases hk2 : k = 2
      · subst hk2
        have he : e = .node "settings" (.root "home" 1) 2 := Option.some.inj hl.symm
        subst he
        exact ⟨by simp [BackstackEntry.toChain], rfl⟩
      · by_cases hk1 : k = 1
        · subst hk1
          have he : e = .root "home" 1 := Option.some.inj hl.symm
          subst he
          exact ⟨by simp [BackstackEntry.toChain], rfl⟩
        · have hne2 : (2 == k) = false := beq_false_of_ne (Ne.symm hk2)
          have hne1 : (1 == k) = false := beq_false_of_ne (Ne.symm hk1)
          simp [mapLookup, hne2, hne1] at hl
    · rintro ⟨hmem, heid⟩
      simp only [BackstackEntry.toChain, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> subst heid <;> rfl

/-- Mutant: popping without checking `previous` fails to reject root-entry pops. -/
def mutantPopBackstackAllowRoot {α : Type} (m : BackstackMap α) (curId : EntryId) : NavResult α :=
  match mapLookup m curId with
  | none => .error .missingEntry
  | some cur =>
    match cur.previous with
    | none => .ok (mapRemove m cur.id) cur.id
    | some prev => .ok (mapRemove m cur.id) prev.id

theorem mutantPopBackstackAllowRoot_violates_root_error :
    let root : BackstackEntry String := .root "home" 1
    mutantPopBackstackAllowRoot [(1, root)] 1 ≠ .error .popLastEntry := by
  decide +kernel

/-- Mutant: non-inclusive `popUpTo` that removes the matched target anyway violates slice preservation. -/
def mutantPopUpToAlwaysInclusive {α : Type} (m : BackstackMap α) (curId targetId : EntryId) : NavResult α :=
  popUpToIdModel m curId targetId true

theorem mutantPopUpToAlwaysInclusive_violates_noninclusive_root :
    let e1 : BackstackEntry String := .root "home" 1
    let e2 : BackstackEntry String := .node "detail" e1 2
    mutantPopUpToAlwaysInclusive [(2, e2), (1, e1)] 2 1 ≠ .ok [(1, e1)] 1 := by
  decide +kernel

end Navigation.Mutations
