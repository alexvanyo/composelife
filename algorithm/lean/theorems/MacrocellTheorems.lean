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
import proofs.MacrocellDagProofs

namespace Algorithm

/-!
# Macrocell Master Theorems

Deserialization returns a well-formed node of bounded depth for every input; serialization reads back as exactly
the same tree for every pattern of smart-constructed nodes; and concrete checks of the format, including the
rejected levels.
-/

/-- Whatever the input, deserialization returns a well-formed node (the children of every node have equal depths,
so building it never fails) of depth at most 63. -/
theorem deserializeMacrocell_wellFormed (lines : Array String) :
    isWellFormed (deserializeMacrocell lines).macroCell ∧ (deserializeMacrocell lines).macroCell.depth ≤ 63 :=
  deserializeMacrocell_wellFormed_Impl lines

/--
Every nonempty pattern of smart-constructed nodes (see `Canonical`), of depth at most 63 and not a single leaf,
reads back as exactly the same tree, with no warnings. The writer numbers nodes by line, so it must write fewer
than 2 ^ 31 lines.
-/
theorem macrocell_round_trip (m : MacroCell) (hcan : Canonical m) (hd : m.depth ≤ 63)
    (hsl : macrocellSingleLeaf m = none) (hne : m ≠ emptyMacroCellUInt32 m.level)
    (hlen : ((⟨[macrocellHeader], [], []⟩ : MacrocellWriterState).addTree m).2.lines.length < 2 ^ 31) :
    deserializeMacrocell (serializeMacrocell m) = ⟨.ok, #[], m⟩ :=
  macrocell_round_trip_Impl m hcan hd hsl hne hlen

/-- A Level 4 node with a single nonempty leaf is written as just that leaf, which reads back in the northwest
quadrant. -/
theorem macrocell_round_trip_single_leaf (m : MacroCell) (leaf : UInt64)
    (hsl : macrocellSingleLeaf m = some leaf) :
    deserializeMacrocell (serializeMacrocell m) = ⟨.ok, #[], makeLevel4Node leaf 0 0 0⟩ :=
  macrocell_round_trip_single_leaf_Impl m leaf hsl

theorem deserializeMacrocell_empty :
    deserializeMacrocell #[] = ⟨.emptyFile, #[.emptyFile], emptyLevel4⟩ :=
  deserializeMacrocell_empty_Impl

theorem deserializeMacrocell_invalid_header :
    deserializeMacrocell #["invalid"] = ⟨.invalidHeader "invalid", #[], emptyLevel4⟩ :=
  deserializeMacrocell_invalid_header_Impl

/-- A node of level 0 is rejected, rather than building empty nodes up to level 2^32 - 1. -/
theorem deserializeMacrocell_level_0 :
    deserializeMacrocell #["[M2]", "0 0 0 0 0"] = ⟨.unexpectedInput ("0 0 0 0 0") 1, #[], emptyLevel4⟩ :=
  deserializeMacrocell_level_0_Impl

/-- A level above 63 is rejected. -/
theorem deserializeMacrocell_level_too_high :
    (deserializeMacrocell #["[M2]", "4000000000 0 0 0 0"]).status = .unexpectedInput "4000000000 0 0 0 0" 1 :=
  deserializeMacrocell_level_too_high_Impl

/-- A child of the wrong level is rejected, with the range of its number. -/
theorem deserializeMacrocell_child_level_mismatch :
    deserializeMacrocell #["[M2]", "*$", "4 1 0 0 0", "6 2 0 0 0"] =
      ⟨.unexpectedNodeId ("6 2 0 0 0") 3 2 2, #[], emptyLevel4⟩ :=
  deserializeMacrocell_child_level_mismatch_Impl

/-- Cells outside the 8 by 8 leaf are ignored. -/
theorem deserializeMacrocell_leaf_bounds :
    deserializeMacrocell #["[M2]", "........*$$$$$$$$*$"] = ⟨.ok, #[], makeLevel4Node 0 0 0 0⟩ :=
  deserializeMacrocell_leaf_bounds_Impl

theorem deserializeMacrocell_single_leaf :
    deserializeMacrocell #["[M2] (ComposeLife 1.0)", "*$"] = ⟨.ok, #[], makeLevel4Node 1 0 0 0⟩ :=
  deserializeMacrocell_single_leaf_Impl

theorem serializeMacrocell_empty : serializeMacrocell emptyLevel4 = #["[M2] (ComposeLife 1.0)"] :=
  serializeMacrocell_empty_Impl

/-- Equal leaves are written once. -/
theorem serializeMacrocell_shared_leaves :
    serializeMacrocell (makeLevel4Node 1 1 0 1) = #["[M2] (ComposeLife 1.0)", "*$", "4 1 1 0 1"] :=
  serializeMacrocell_shared_leaves_Impl

theorem macrocell_round_trip_level4 :
    (deserializeMacrocell (serializeMacrocell (makeLevel4Node 1 2 3 4))).macroCell = makeLevel4Node 1 2 3 4 :=
  macrocell_round_trip_level4_Impl

theorem macrocell_round_trip_level5 :
    (deserializeMacrocell (serializeMacrocell
      (makeCellNode (makeLevel4Node 1 0 0 0) emptyLevel4 emptyLevel4 (makeLevel4Node 1 0 0 0)))).macroCell =
      makeCellNode (makeLevel4Node 1 0 0 0) emptyLevel4 emptyLevel4 (makeLevel4Node 1 0 0 0) :=
  macrocell_round_trip_level5_Impl

/--
Round trip of the writer that runs: `serializeMacrocellDag` writes the distinct subtrees `entries` of a tree (children
first, the tree last, with the entry numbers of each node's children in `kids`) with hash tables, and its lines read
back as the tree, for the same trees as `macrocell_round_trip`.
-/
theorem macrocell_dag_round_trip (entries : Array MacroCell) (kids : Array UInt32) (hwf : DagWF entries kids)
    (h0 : 0 < entries.size) (hn : entries.size < 2 ^ 29)
    (hcan : ∀ m ∈ entries, Canonical m ∧ m.depth ≤ 63)
    (hlev : ∀ j < entries.size - 1, entries[j]!.level.toNat < entries[entries.size - 1]!.level.toNat)
    (hsl : macrocellSingleLeaf entries[entries.size - 1]! = none)
    (hne : entries[entries.size - 1]! ≠ emptyMacroCellUInt32 entries[entries.size - 1]!.level)
    (hlen : (addTrees ⟨[macrocellHeader], [], []⟩ entries.toList).lines.length < 2 ^ 31) :
    deserializeMacrocell (serializeMacrocellDag entries kids) = ⟨.ok, #[], entries[entries.size - 1]!⟩ :=
  macrocell_dag_round_trip_Impl entries kids hwf h0 hn hcan hlev hsl hne hlen

/-- A single leaf is written by the DAG writer as by `serializeMacrocell`. -/
theorem serializeMacrocellDag_single_leaf (entries : Array MacroCell) (kids : Array UInt32)
    (h0 : 0 < entries.size) (hs : entries.size < 2 ^ 32) (leaf : UInt64)
    (hsl : macrocellSingleLeaf entries[entries.size - 1]! = some leaf) :
    serializeMacrocellDag entries kids = serializeMacrocell entries[entries.size - 1]! :=
  serializeMacrocellDag_single_leaf_Impl entries kids h0 hs leaf hsl

end Algorithm
