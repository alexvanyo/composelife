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

import proofs.BackstackNavigationModelProofs

namespace Navigation.Model

theorem navigate_preserves_wellFormed {α : Type}
    (m : BackstackMap α) (curId : EntryId) (vf : BackstackEntry α → α) (freshId : EntryId)
    (hwf : WellFormedBackstack m curId) (hfresh : mapLookup m freshId = none) :
    ∃ head' m',
      navigateModel m curId vf freshId = .ok m' freshId ∧
      WellFormedBackstack m' freshId ∧
      mapLookup m' freshId = some head' ∧
      (∀ k, mapLookup m k ≠ none → mapLookup m' k = mapLookup m k) ∧
      (∀ head, mapLookup m curId = some head → head'.depth = head.depth + 1) :=
  navigate_preserves_wellFormed_Impl m curId vf freshId hwf hfresh

theorem popBackstack_throws_on_root {α : Type}
    (m : BackstackMap α) (curId : EntryId) (head : BackstackEntry α)
    (hhead : mapLookup m curId = some head) (hdepth : head.depth = 1) :
    popBackstackModel m curId = .error .popLastEntry :=
  popBackstack_throws_on_root_Impl m curId head hhead hdepth

theorem popBackstack_preserves_wellFormed {α : Type}
    (m : BackstackMap α) (curId : EntryId) (head prev : BackstackEntry α)
    (hwf : WellFormedBackstack m curId)
    (hhead : mapLookup m curId = some head)
    (hprev : head.previous = some prev) :
    popBackstackModel m curId = .ok (mapRemove m head.id) prev.id ∧
    WellFormedBackstack (mapRemove m head.id) prev.id ∧
    mapLookup (mapRemove m head.id) head.id = none ∧
    (∀ k, k ≠ head.id → mapLookup (mapRemove m head.id) k = mapLookup m k) :=
  popBackstack_preserves_wellFormed_Impl m curId head prev hwf hhead hprev

theorem popBackstack_navigate_inverse {α : Type}
    (m : BackstackMap α) (curId : EntryId) (vf : BackstackEntry α → α) (freshId : EntryId)
    (hwf : WellFormedBackstack m curId) (hfresh : mapLookup m freshId = none) :
    match navigateModel m curId vf freshId with
    | .ok m' newId => popBackstackModel m' newId = .ok m curId
    | .error _ => False :=
  popBackstack_navigate_inverse_Impl m curId vf freshId hwf hfresh

theorem popUpTo_terminates_and_slices {α : Type}
    (m : BackstackMap α) (curId : EntryId) (pred : BackstackEntry α → Bool)
    (inclusive : Bool) (head : BackstackEntry α) (k : Nat)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hk : matchDistance? pred head = some k) :
    popUpToWalk pred m head = popUpToWalkFuel pred k m head ∧
    ∃ target, head.toChain[k]? = some target ∧
    if inclusive then
      match target.previous with
      | none => popUpToModel m curId pred true = .error .popLastEntry
      | some prev =>
        ∃ m',
          popUpToModel m curId pred true = .ok m' prev.id ∧
          WellFormedBackstack m' prev.id ∧
          (∀ e ∈ head.toChain.take (k + 1), mapLookup m' e.id = none) ∧
          (∀ e ∈ head.toChain.drop (k + 1), mapLookup m' e.id = some e)
    else
      ∃ m',
        popUpToModel m curId pred false = .ok m' target.id ∧
        WellFormedBackstack m' target.id ∧
        (∀ e ∈ head.toChain.take k, mapLookup m' e.id = none) ∧
        (∀ e ∈ head.toChain.drop k, mapLookup m' e.id = some e) :=
  popUpTo_terminates_and_slices_Impl m curId pred inclusive head k hwf hhead hk

theorem popUpTo_throws_when_no_match {α : Type}
    (m : BackstackMap α) (curId : EntryId) (pred : BackstackEntry α → Bool)
    (inclusive : Bool) (head : BackstackEntry α)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hnone : matchDistance? pred head = none) :
    popUpToModel m curId pred inclusive = .error .predicateNotFound :=
  popUpTo_throws_when_no_match_Impl m curId pred inclusive head hwf hhead hnone

theorem popUpToId_slices_to_ancestor {α : Type}
    (m : BackstackMap α) (curId targetId : EntryId) (inclusive : Bool)
    (head : BackstackEntry α) (k : Nat)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hk : matchDistance? (fun e => e.id == targetId) head = some k) :
    ∃ target, head.toChain[k]? = some target ∧
    target.id = targetId ∧
    if inclusive then
      match target.previous with
      | none => popUpToIdModel m curId targetId true = .error .popLastEntry
      | some prev =>
        ∃ m',
          popUpToIdModel m curId targetId true = .ok m' prev.id ∧
          WellFormedBackstack m' prev.id
    else
      ∃ m',
        popUpToIdModel m curId targetId false = .ok m' targetId ∧
        WellFormedBackstack m' targetId :=
  popUpToId_slices_to_ancestor_Impl m curId targetId inclusive head k hwf hhead hk

theorem popUpToValue_slices_to_matching_value {α : Type}
    (m : BackstackMap α) (curId : EntryId) (pred : α → Bool) (inclusive : Bool)
    (head : BackstackEntry α) (k : Nat)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hk : matchDistance? (fun e => pred e.value) head = some k) :
    popUpToWalk (fun e => pred e.value) m head =
      popUpToWalkFuel (fun e => pred e.value) k m head ∧
    ∃ target, head.toChain[k]? = some target ∧
    if inclusive then
      match target.previous with
      | none => popUpToValueModel m curId pred true = .error .popLastEntry
      | some prev =>
        ∃ m',
          popUpToValueModel m curId pred true = .ok m' prev.id ∧
          WellFormedBackstack m' prev.id
    else
      ∃ m',
        popUpToValueModel m curId pred false = .ok m' target.id ∧
        WellFormedBackstack m' target.id :=
  popUpToValue_slices_to_matching_value_Impl m curId pred inclusive head k hwf hhead hk

end Navigation.Model
