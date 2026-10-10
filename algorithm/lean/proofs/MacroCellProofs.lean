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
import Algorithm.BitComputation
import Algorithm.MacroCell

namespace Algorithm

theorem hashlife_empty_level2_stability_Impl :
    hashLifeStepLevel2 (emptyNode 2) = emptyNode 1 := by
  rfl

theorem hashlife_block_preservation_Impl :
    let nw := makeLevel1 false false false true   -- (1, 1) is active
    let ne := makeLevel1 false false true false   -- (2, 1) is active
    let sw := makeLevel1 false true false false   -- (1, 2) is active
    let se := makeLevel1 true false false false   -- (2, 2) is active
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 block4x4 = makeLevel1 true true true true := by
  decide

theorem hashlife_blinker_oscillation_Impl :
    let nw := makeLevel1 false false false true   -- (1, 1) is active
    let ne := makeLevel1 false false true true    -- (2, 1) and (3, 1) are active
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 blinker4x4 = makeLevel1 false true false true := by
  decide

theorem hashlife_tub_preservation_Impl :
    let nw := makeLevel1 false true true false    -- (1, 0) and (0, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false false false false
    let tub4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 tub4x4 = makeLevel1 false true true false := by
  decide

theorem centered_subnode_level_correct_Impl
    (nw_se ne_sw sw_ne se_nw : MacroCell)
    (nw_nw nw_ne nw_sw : MacroCell)
    (ne_nw ne_ne ne_se : MacroCell)
    (sw_nw sw_sw sw_se : MacroCell)
    (se_ne se_sw se_se : MacroCell) :
    let nw := MacroCell.node 2 nw_nw nw_ne nw_sw nw_se
    let ne := MacroCell.node 2 ne_nw ne_ne ne_sw ne_se
    let sw := MacroCell.node 2 sw_nw sw_ne sw_sw sw_se
    let se := MacroCell.node 2 se_nw se_ne se_sw se_se
    (centeredSubnode (.node 3 nw ne sw se)).level = 2 := by
  rfl

end Algorithm
