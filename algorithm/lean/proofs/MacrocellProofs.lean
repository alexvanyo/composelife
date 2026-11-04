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

import Algorithm.MacroCell

namespace Algorithm

theorem serializeMacrocell_empty_Impl :
    serializeMacrocell emptyLevel4 = #["[M2] (ComposeLife 1.0)"] := by
  decide +kernel

theorem formatLeafNode_zero_Impl :
    formatLeafNode 0 = "$" := by
  decide +kernel

theorem parseLeafNode_dollar_Impl :
    parseLeafNode "$" = 0 := by
  decide +kernel

theorem parseLeafNode_star_dollar_Impl :
    parseLeafNode "*$" = 1 := by
  decide +kernel

theorem formatLeafNode_one_Impl :
    formatLeafNode 1 = "*$" := by
  decide +kernel

theorem leafContains_star_dollar_Impl :
    leafContains (parseLeafNode "*$") 0 0 = true := by
  decide +kernel

theorem parseLeafNode_empty_Impl :
    parseLeafNode "" = 0 := by
  decide +kernel

theorem macrocell_leaf_roundtrip_zero_Impl :
    parseLeafNode (formatLeafNode 0) = 0 := by
  decide +kernel

theorem macrocell_leaf_roundtrip_one_Impl :
    parseLeafNode (formatLeafNode 1) = 1 := by
  decide +kernel

theorem macrocell_leaf_roundtrip_row1_Impl :
    parseLeafNode (formatLeafNode ((1 : UInt64) <<< 8)) = ((1 : UInt64) <<< 8) := by
  decide +kernel

theorem macrocell_leaf_roundtrip_last_bit_Impl :
    parseLeafNode (formatLeafNode ((1 : UInt64) <<< 63)) = ((1 : UInt64) <<< 63) := by
  decide +kernel

theorem macrocell_leaf_roundtrip_all_ones_Impl :
    parseLeafNode (formatLeafNode (~~~(0 : UInt64))) = ~~~(0 : UInt64) := by
  decide +kernel

theorem macrocell_leaf_roundtrip_checkerboard_Impl :
    parseLeafNode (formatLeafNode 0x5555555555555555) = 0x5555555555555555 := by
  decide +kernel

theorem macrocell_leaf_roundtrip_inv_checkerboard_Impl :
    parseLeafNode (formatLeafNode 0xAAAAAAAAAAAAAAAA) = 0xAAAAAAAAAAAAAAAA := by
  decide +kernel

theorem macrocell_leaf_roundtrip_full_row0_Impl :
    parseLeafNode (formatLeafNode 0xFF) = 0xFF := by
  decide +kernel

theorem macrocell_leaf_roundtrip_full_col0_Impl :
    parseLeafNode (formatLeafNode 0x0101010101010101) = 0x0101010101010101 := by
  decide +kernel

def makeLeafRow (w : UInt8) (y : UInt32) : UInt64 :=
  let b0 := if (w &&& 1) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 0 y).toUInt64) else 0
  let b1 := if (w &&& 2) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 1 y).toUInt64) else 0
  let b2 := if (w &&& 4) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 2 y).toUInt64) else 0
  let b3 := if (w &&& 8) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 3 y).toUInt64) else 0
  let b4 := if (w &&& 16) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 4 y).toUInt64) else 0
  let b5 := if (w &&& 32) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 5 y).toUInt64) else 0
  let b6 := if (w &&& 64) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 6 y).toUInt64) else 0
  let b7 := if (w &&& 128) != 0 then ((1 : UInt64) <<< (cellToLeafBitUInt 7 y).toUInt64) else 0
  b0 ||| b1 ||| b2 ||| b3 ||| b4 ||| b5 ||| b6 ||| b7

def allSingleBitsRoundTrip : Bool :=
  (List.range 64).all fun k =>
    let leaf : UInt64 := (1 : UInt64) <<< k.toUInt64
    parseLeafNode (formatLeafNode leaf) == leaf

def allSingleRowsRoundTrip : Bool :=
  (List.range 8).all fun y =>
    (List.range 256).all fun n =>
      let w := n.toUInt8
      let leaf := makeLeafRow w y.toUInt32
      parseLeafNode (formatLeafNode leaf) == leaf

theorem macrocell_leaf_roundtrip_all_single_bits_Impl :
    allSingleBitsRoundTrip = true := by
  decide +kernel

theorem macrocell_leaf_roundtrip_all_single_bits_universal_Impl (k : Nat) (hk : k < 64) :
    parseLeafNode (formatLeafNode ((1 : UInt64) <<< k.toUInt64)) = (1 : UInt64) <<< k.toUInt64 := by
  have hall := macrocell_leaf_roundtrip_all_single_bits_Impl
  dsimp [allSingleBitsRoundTrip] at hall
  rw [List.all_eq_true] at hall
  have hin : k ∈ List.range 64 := List.mem_range.mpr hk
  have htest := hall k hin
  exact of_decide_eq_true htest

theorem macrocell_leaf_roundtrip_all_single_rows_Impl :
    allSingleRowsRoundTrip = true := by
  decide +kernel

theorem macrocell_leaf_roundtrip_all_single_rows_universal_Impl (y : Nat) (hy : y < 8) (n : Nat) (hn : n < 256) :
    let w := n.toUInt8
    let leaf := makeLeafRow w y.toUInt32
    parseLeafNode (formatLeafNode leaf) = leaf := by
  have hall := macrocell_leaf_roundtrip_all_single_rows_Impl
  dsimp [allSingleRowsRoundTrip] at hall
  rw [List.all_eq_true] at hall
  have hy_in : y ∈ List.range 8 := List.mem_range.mpr hy
  have hy_all := hall y hy_in
  rw [List.all_eq_true] at hy_all
  have hn_in : n ∈ List.range 256 := List.mem_range.mpr hn
  have htest := hy_all n hn_in
  exact of_decide_eq_true htest

theorem deserializeMacrocell_empty_Impl :
    deserializeMacrocell #[] = ⟨1, "", 0, 0, 0, 0, #[⟨0, 0, 0, ""⟩], emptyLevel4⟩ := by
  unfold deserializeMacrocell
  rfl

theorem deserializeMacrocell_header_only_Impl :
    deserializeMacrocell #["[M2] (ComposeLife 1.0)"] = ⟨0, "", 0, 0, 0, 0, #[], emptyLevel4⟩ := by
  decide +kernel

theorem deserializeMacrocell_invalid_header_Impl :
    deserializeMacrocell #["[INVALID]"] = ⟨2, "[INVALID]", 1, 0, 0, 0, #[], emptyLevel4⟩ := by
  decide +kernel

theorem deserializeMacrocell_single_leaf_Impl :
    deserializeMacrocell #["[M2] (ComposeLife 1.0)", "*$"] =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node 1 0 0 0⟩ := by
  decide +kernel

theorem macrocell_roundtrip_empty_Impl :
    deserializeMacrocell (serializeMacrocell emptyLevel4) =
    ⟨0, "", 0, 0, 0, 0, #[], emptyLevel4⟩ := by
  decide +kernel

theorem macrocell_roundtrip_single_leaf_Impl :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node 1 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node 1 0 0 0⟩ := by
  decide +kernel

theorem macrocell_roundtrip_row1_Impl :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node ((1 : UInt64) <<< 8) 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node ((1 : UInt64) <<< 8) 0 0 0⟩ := by
  decide +kernel

theorem macrocell_roundtrip_last_bit_Impl :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node ((1 : UInt64) <<< 63) 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node ((1 : UInt64) <<< 63) 0 0 0⟩ := by
  decide +kernel

theorem macrocell_roundtrip_all_ones_Impl :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node (~~~(0 : UInt64)) 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node (~~~(0 : UInt64)) 0 0 0⟩ := by
  decide +kernel

theorem macrocell_roundtrip_full_level4_Impl :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node 1 2 3 4)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node 1 2 3 4⟩ := by
  decide +kernel

theorem macrocell_roundtrip_level5_cellnode_Impl :
    deserializeMacrocell (serializeMacrocell (makeCellNode (makeLevel4Node 1 0 0 0) emptyLevel4 emptyLevel4 emptyLevel4)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeCellNode (makeLevel4Node 1 0 0 0) emptyLevel4 emptyLevel4 emptyLevel4⟩ := by
  decide +kernel

end Algorithm
