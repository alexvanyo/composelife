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
import AlgorithmDefs
import proofs.PropertiesProofs
import proofs.SymmetryProofs
import proofs.GridEquivalenceProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Properties of Conway's rule on finite grids
-/

theorem extinction_stability (n : ℕ) :
    stepN n [] = [] :=
  extinction_stability_Impl n

/-- Speed of light: every live cell of the next generation is a Moore neighbor (or itself) of a live cell. -/
theorem stepGrid_speed_of_light (s : List Coord) (c : Coord) (hc : c ∈ stepGrid s) :
    ∃ p ∈ s, max (c.1 - p.1).natAbs (c.2 - p.2).natAbs ≤ 1 :=
  stepGrid_support s c hc

/-- Conway's rule commutes with every translation. -/
theorem stepGrid_translate_comm (dx dy : ℤ) (s : List Coord) :
    cellsEqual (stepGrid (translateGrid dx dy s)) (translateGrid dx dy (stepGrid s)) = true :=
  stepGrid_translate_Impl dx dy s

/-- Conway's rule commutes with the reflection across the x axis. -/
theorem stepGrid_flipX_comm (s : List Coord) :
    cellsEqual (stepGrid (flipXGrid s)) (flipXGrid (stepGrid s)) = true :=
  stepGrid_flipX_Impl s

/-- Conway's rule commutes with the reflection across the y axis. -/
theorem stepGrid_flipY_comm (s : List Coord) :
    cellsEqual (stepGrid (flipYGrid s)) (flipYGrid (stepGrid s)) = true :=
  stepGrid_flipY_Impl s

/-- Conway's rule commutes with the reflection across the diagonal. -/
theorem stepGrid_flipDiag_comm (s : List Coord) :
    cellsEqual (stepGrid (flipDiagGrid s)) (flipDiagGrid (stepGrid s)) = true :=
  stepGrid_flipDiag_Impl s

/-- Conway's rule commutes with the rotation by 90 degrees. -/
theorem stepGrid_rotate90_comm (s : List Coord) :
    cellsEqual (stepGrid (rotate90Grid s)) (rotate90Grid (stepGrid s)) = true :=
  stepGrid_rotate90_Impl s

end Algorithm
