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

local notation "ℕ" => Nat

namespace Algorithm

theorem stepN_composition_step (n : ℕ) (s : List Coord) :
    stepN (n + 1) s = stepGrid (stepN n s) :=
  stepN_composition_step_Impl n s

theorem extinction_stability (n : ℕ) :
    stepN n [] = [] :=
  extinction_stability_Impl n

theorem blinker_translation_commutes :
    let b := [(0, 1), (1, 1), (2, 1)]
    let tb := translateGrid 157 72 b
    cellsEqual (stepGrid tb) (translateGrid 157 72 (stepGrid b)) = true :=
  blinker_translation_commutes_Impl

theorem blinker_flipX_commutes :
    let b := [(0, 1), (1, 1), (2, 1)]
    cellsEqual (stepGrid (flipXGrid b)) (flipXGrid (stepGrid b)) = true :=
  blinker_flipX_commutes_Impl

theorem blinker_flipY_commutes :
    let b := [(0, 1), (1, 1), (2, 1)]
    cellsEqual (stepGrid (flipYGrid b)) (flipYGrid (stepGrid b)) = true :=
  blinker_flipY_commutes_Impl

theorem blinker_flipDiag_commutes :
    let b := [(0, 1), (1, 1), (2, 1)]
    cellsEqual (stepGrid (flipDiagGrid b)) (flipDiagGrid (stepGrid b)) = true :=
  blinker_flipDiag_commutes_Impl

theorem glider_translation_commutes :
    let g := [(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]
    let tg := translateGrid 157 72 g
    cellsEqual (stepGrid tg) (translateGrid 157 72 (stepGrid g)) = true :=
  glider_translation_commutes_Impl

end Algorithm
