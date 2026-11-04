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
import proofs.MacrocellProofs

namespace Algorithm

theorem serializeMacrocell_empty :
    serializeMacrocell emptyLevel4 = #["[M2] (ComposeLife 1.0)"] :=
  serializeMacrocell_empty_Impl

theorem formatLeafNode_zero :
    formatLeafNode 0 = "$" :=
  formatLeafNode_zero_Impl

theorem parseLeafNode_dollar :
    parseLeafNode "$" = 0 :=
  parseLeafNode_dollar_Impl

theorem parseLeafNode_star_dollar :
    parseLeafNode "*$" = 1 :=
  parseLeafNode_star_dollar_Impl

theorem formatLeafNode_one :
    formatLeafNode 1 = "*$" :=
  formatLeafNode_one_Impl

theorem leafContains_star_dollar :
    leafContains (parseLeafNode "*$") 0 0 = true :=
  leafContains_star_dollar_Impl

theorem parseLeafNode_empty :
    parseLeafNode "" = 0 :=
  parseLeafNode_empty_Impl

theorem macrocell_leaf_roundtrip_zero :
    parseLeafNode (formatLeafNode 0) = 0 :=
  macrocell_leaf_roundtrip_zero_Impl

theorem macrocell_leaf_roundtrip_one :
    parseLeafNode (formatLeafNode 1) = 1 :=
  macrocell_leaf_roundtrip_one_Impl

theorem macrocell_leaf_roundtrip_row1 :
    parseLeafNode (formatLeafNode ((1 : UInt64) <<< 8)) = ((1 : UInt64) <<< 8) :=
  macrocell_leaf_roundtrip_row1_Impl

theorem macrocell_leaf_roundtrip_last_bit :
    parseLeafNode (formatLeafNode ((1 : UInt64) <<< 63)) = ((1 : UInt64) <<< 63) :=
  macrocell_leaf_roundtrip_last_bit_Impl

theorem macrocell_leaf_roundtrip_all_ones :
    parseLeafNode (formatLeafNode (~~~(0 : UInt64))) = ~~~(0 : UInt64) :=
  macrocell_leaf_roundtrip_all_ones_Impl

theorem macrocell_leaf_roundtrip_checkerboard :
    parseLeafNode (formatLeafNode 0x5555555555555555) = 0x5555555555555555 :=
  macrocell_leaf_roundtrip_checkerboard_Impl

theorem macrocell_leaf_roundtrip_inv_checkerboard :
    parseLeafNode (formatLeafNode 0xAAAAAAAAAAAAAAAA) = 0xAAAAAAAAAAAAAAAA :=
  macrocell_leaf_roundtrip_inv_checkerboard_Impl

theorem macrocell_leaf_roundtrip_full_row0 :
    parseLeafNode (formatLeafNode 0xFF) = 0xFF :=
  macrocell_leaf_roundtrip_full_row0_Impl

theorem macrocell_leaf_roundtrip_full_col0 :
    parseLeafNode (formatLeafNode 0x0101010101010101) = 0x0101010101010101 :=
  macrocell_leaf_roundtrip_full_col0_Impl

theorem macrocell_leaf_roundtrip_all_single_bits :
    allSingleBitsRoundTrip = true :=
  macrocell_leaf_roundtrip_all_single_bits_Impl

theorem macrocell_leaf_roundtrip_all_single_bits_universal (k : Nat) (hk : k < 64) :
    parseLeafNode (formatLeafNode ((1 : UInt64) <<< k.toUInt64)) = (1 : UInt64) <<< k.toUInt64 :=
  macrocell_leaf_roundtrip_all_single_bits_universal_Impl k hk

theorem macrocell_leaf_roundtrip_all_single_rows :
    allSingleRowsRoundTrip = true :=
  macrocell_leaf_roundtrip_all_single_rows_Impl

theorem macrocell_leaf_roundtrip_all_single_rows_universal (y : Nat) (hy : y < 8) (n : Nat) (hn : n < 256) :
    let w := n.toUInt8
    let leaf := makeLeafRow w y.toUInt32
    parseLeafNode (formatLeafNode leaf) = leaf :=
  macrocell_leaf_roundtrip_all_single_rows_universal_Impl y hy n hn

theorem deserializeMacrocell_empty :
    deserializeMacrocell #[] = ⟨1, "", 0, 0, 0, 0, #[⟨0, 0, 0, ""⟩], emptyLevel4⟩ :=
  deserializeMacrocell_empty_Impl

theorem deserializeMacrocell_header_only :
    deserializeMacrocell #["[M2] (ComposeLife 1.0)"] = ⟨0, "", 0, 0, 0, 0, #[], emptyLevel4⟩ :=
  deserializeMacrocell_header_only_Impl

theorem deserializeMacrocell_invalid_header :
    deserializeMacrocell #["[INVALID]"] = ⟨2, "[INVALID]", 1, 0, 0, 0, #[], emptyLevel4⟩ :=
  deserializeMacrocell_invalid_header_Impl

theorem deserializeMacrocell_single_leaf :
    deserializeMacrocell #["[M2] (ComposeLife 1.0)", "*$"] =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node 1 0 0 0⟩ :=
  deserializeMacrocell_single_leaf_Impl

theorem macrocell_roundtrip_empty :
    deserializeMacrocell (serializeMacrocell emptyLevel4) =
    ⟨0, "", 0, 0, 0, 0, #[], emptyLevel4⟩ :=
  macrocell_roundtrip_empty_Impl

theorem macrocell_roundtrip_single_leaf :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node 1 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node 1 0 0 0⟩ :=
  macrocell_roundtrip_single_leaf_Impl

theorem macrocell_roundtrip_row1 :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node ((1 : UInt64) <<< 8) 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node ((1 : UInt64) <<< 8) 0 0 0⟩ :=
  macrocell_roundtrip_row1_Impl

theorem macrocell_roundtrip_last_bit :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node ((1 : UInt64) <<< 63) 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node ((1 : UInt64) <<< 63) 0 0 0⟩ :=
  macrocell_roundtrip_last_bit_Impl

theorem macrocell_roundtrip_all_ones :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node (~~~(0 : UInt64)) 0 0 0)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node (~~~(0 : UInt64)) 0 0 0⟩ :=
  macrocell_roundtrip_all_ones_Impl

theorem macrocell_roundtrip_full_level4 :
    deserializeMacrocell (serializeMacrocell (makeLevel4Node 1 2 3 4)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeLevel4Node 1 2 3 4⟩ :=
  macrocell_roundtrip_full_level4_Impl

theorem macrocell_roundtrip_level5_cellnode :
    deserializeMacrocell (serializeMacrocell (makeCellNode (makeLevel4Node 1 0 0 0) emptyLevel4 emptyLevel4 emptyLevel4)) =
    ⟨0, "", 0, 0, 0, 0, #[], makeCellNode (makeLevel4Node 1 0 0 0) emptyLevel4 emptyLevel4 emptyLevel4⟩ :=
  macrocell_roundtrip_level5_cellnode_Impl

end Algorithm
