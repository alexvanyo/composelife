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

import models.CellStateModel

namespace Algorithm.KotlinModel

theorem withCellModel_true_mem_Impl (cells : List UInt64) (p : UInt64) :
    (withCellModel cells p true).contains p = true := by
  unfold withCellModel
  cases h : cells.contains p
  · simp
  · simp only [↓reduceIte]; exact h

theorem withCellModel_false_not_mem_Impl (cells : List UInt64) (p : UInt64) :
    (withCellModel cells p false).contains p = false := by
  unfold withCellModel
  simp

theorem cellStateEqualsModel_refl_Impl (cells : List UInt64) :
    cellStateEqualsModel cells cells = true := by
  unfold cellStateEqualsModel
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro x hx
  exact List.contains_iff_exists_mem_beq.mpr ⟨x, hx, beq_self_eq_true x⟩

theorem boundingBoxModel_empty_Impl :
    boundingBoxModel [] = (0, 0, 0, 0) := rfl

theorem boundingBoxModel_singleton_Impl (p : UInt64) :
    boundingBoxModel [p] = (cellOffsetX p, cellOffsetY p, cellOffsetX p + 1, cellOffsetY p + 1) := rfl

end Algorithm.KotlinModel
