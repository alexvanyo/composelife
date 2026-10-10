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
import Algorithm.Patterns
import AlgorithmDefs
import proofs.PatternsProofs

namespace Algorithm

theorem block_is_still_life :
    sameCells (stepGrid blockPattern) blockPattern = true :=
  block_is_still_life_Impl

theorem tub_is_still_life :
    sameCells (stepGrid tubPattern) tubPattern = true :=
  tub_is_still_life_Impl

theorem blinker_period_two :
    sameCells (stepGrid blinkerH) blinkerV = true ∧
    sameCells (stepGrid blinkerV) blinkerH = true ∧
    sameCells (stepN 2 blinkerH) blinkerH = true :=
  blinker_period_two_Impl

theorem glider_period_four_shift :
    let g4 := stepN 4 gliderPattern
    let shifted := gliderPattern.map (fun (x, y) => (x + 1, y + 1))
    sameCells g4 shifted = true :=
  glider_period_four_shift_Impl

end Algorithm
