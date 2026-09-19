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
import Algorithm.HashLife

namespace Algorithm

@[export algorithm_step_4x4_bits]
def oracleStep4x4Bits (bits : Nat) : Nat :=
  computeNextGen4x4 bits

@[export algorithm_step_leaf_bits]
def oracleStepLeafBits (bits : Nat) : Nat :=
  computeLeafNextGen8x8Branch bits

@[export algorithm_step_level4_bits]
def oracleStepLevel4Bits (nw ne sw se : Nat) : Nat :=
  computeLevel4NextGen16x16 nw ne sw se

@[export algorithm_centered_subnode_level3_bits]
def oracleCenteredSubnodeLevel3Bits (leaf : Nat) : Nat :=
  centeredSubnodeLevel3Bits leaf

@[export algorithm_centered_horizontal_subnode_level3_bits]
def oracleCenteredHorizontalSubnodeLevel3Bits (w e : Nat) : Nat :=
  centeredHorizontalSubnodeLevel3Bits w e

@[export algorithm_centered_vertical_subnode_level3_bits]
def oracleCenteredVerticalSubnodeLevel3Bits (n s : Nat) : Nat :=
  centeredVerticalSubnodeLevel3Bits n s

@[export algorithm_centered_sub_subnode_level4_bits]
def oracleCenteredSubSubnodeLevel4Bits (nw ne sw se : Nat) : Nat :=
  centeredSubSubnodeLevel4Bits nw ne sw se

@[export algorithm_step_coords]
def oracleStepCoords (coords : Array (Int × Int)) (steps : Nat) : Array (Int × Int) :=
  let inputList := coords.toList
  let resultList := stepN steps inputList
  resultList.toArray

end Algorithm
