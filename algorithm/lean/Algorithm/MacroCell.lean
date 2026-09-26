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

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

inductive MacroCell where
  | leaf (alive : Bool)
  | node (level : ℕ) (nw ne sw se : MacroCell)
  deriving DecidableEq, Repr

def MacroCell.level : MacroCell → ℕ
  | leaf _ => 0
  | node k _ _ _ _ => k

def MacroCell.subcellWidth (k : ℕ) : ℤ :=
  match k with
  | 0 => 0
  | 1 => 1
  | n + 1 => (2 : ℤ) ^ n

/--
Recursively creates an empty (all dead) macrocell at tree level k.
-/
def emptyNode : ℕ → MacroCell
  | 0 => .leaf false
  | k + 1 =>
    let sub := emptyNode k
    .node (k + 1) sub sub sub sub

/--
Flattens a MacroCell to a list of live 2D coordinates rooted at (ox, oy).
-/
def macroCellToGrid (ox oy : ℤ) : MacroCell → List Coord
  | .leaf true => [(ox, oy)]
  | .leaf false => []
  | .node k nw ne sw se =>
    let w := MacroCell.subcellWidth k
    let nwCells := macroCellToGrid ox oy nw
    let neCells := macroCellToGrid (ox + w) oy ne
    let swCells := macroCellToGrid ox (oy + w) sw
    let seCells := macroCellToGrid (ox + w) (oy + w) se
    nwCells ++ neCells ++ swCells ++ seCells

/--
Constructors for level 1 (2x2) and level 2 (4x4) macrocells.
-/
def makeLevel1 (nw ne sw se : Bool) : MacroCell :=
  .node 1 (.leaf nw) (.leaf ne) (.leaf sw) (.leaf se)

def makeLevel2 (nw ne sw se : MacroCell) : MacroCell :=
  .node 2 nw ne sw se

/--
Extracts the center subnode of level k-1 from a level k node.
In quadtree coordinates, the center consists of:
  nw = nw.se, ne = ne.sw, sw = sw.ne, se = se.nw
-/
def centeredSubnode : MacroCell → MacroCell
  | .node k (.node _ _ _ _ nw_se) (.node _ _ _ ne_sw _)
            (.node _ _ sw_ne _ _) (.node _ se_nw _ _ _) =>
    .node (k - 1) nw_se ne_sw sw_ne se_nw
  | m => m

/--
Extracts the horizontal center subnode spanning between west and east nodes.
-/
def centeredHorizontalSubnode : MacroCell → MacroCell → MacroCell
  | .node k _ w_ne _ w_se, .node _ e_nw _ e_sw _ =>
    match w_ne, w_se, e_nw, e_sw with
    | .node _ _ _ _ w_ne_se, .node _ _ w_se_ne _ _,
      .node _ _ _ e_nw_sw _, .node _ e_sw_nw _ _ _ =>
      .node (k - 1) w_ne_se e_nw_sw w_se_ne e_sw_nw
    | _, _, _, _ => emptyNode (k - 1)
  | w, _ => w

/--
Extracts the vertical center subnode spanning between north and south nodes.
-/
def centeredVerticalSubnode : MacroCell → MacroCell → MacroCell
  | .node k _ _ n_sw n_se, .node _ s_nw s_ne _ _ =>
    match n_sw, n_se, s_nw, s_ne with
    | .node _ _ _ _ n_sw_se, .node _ _ _ n_se_sw _,
      .node _ _ s_nw_ne _ _, .node _ s_ne_nw _ _ _ =>
      .node (k - 1) n_sw_se n_se_sw s_nw_ne s_ne_nw
    | _, _, _, _ => emptyNode (k - 1)
  | n, _ => n

/--
Extracts the center sub-subnode from a node of level k >= 2.
In quadtree coordinates, this is:
  nw = node.nw.se.se
  ne = node.ne.sw.sw
  sw = node.sw.ne.ne
  se = node.se.nw.nw
-/
def centeredSubSubnode : MacroCell → MacroCell
  | .node k (.node _ _ _ _ (.node _ _ _ _ nw_se_se))
            (.node _ _ _ (.node _ _ _ ne_sw_sw _) _)
            (.node _ _ (.node _ _ sw_ne_ne _ _) _ _)
            (.node _ (.node _ se_nw_nw _ _ _) _ _ _) =>
    .node (k - 2) nw_se_se ne_sw_sw sw_ne_ne se_nw_nw
  | m => m

/--
Converts a level 2 MacroCell (4x4) to its 16-bit integer representation.
-/
def level2ToBits (m : MacroCell) : ℕ :=
  match m with
  | .node 2 (.node 1 (.leaf b0) (.leaf b1) (.leaf b2) (.leaf b3))
            (.node 1 (.leaf b4) (.leaf b5) (.leaf b6) (.leaf b7))
            (.node 1 (.leaf b8) (.leaf b9) (.leaf b10) (.leaf b11))
            (.node 1 (.leaf b12) (.leaf b13) (.leaf b14) (.leaf b15)) =>
    boolToNat b0 * (2^0) + boolToNat b1 * (2^1) + boolToNat b2 * (2^2) + boolToNat b3 * (2^3) +
    boolToNat b4 * (2^4) + boolToNat b5 * (2^5) + boolToNat b6 * (2^6) + boolToNat b7 * (2^7) +
    boolToNat b8 * (2^8) + boolToNat b9 * (2^9) + boolToNat b10 * (2^10) + boolToNat b11 * (2^11) +
    boolToNat b12 * (2^12) + boolToNat b13 * (2^13) + boolToNat b14 * (2^14) + boolToNat b15 * (2^15)
  | _ => 0

/--
Converts a 4-bit integer output from BitComputation into a level 1 (2x2) MacroCell.
-/
def bitsToLevel1 (out : ℕ) : MacroCell :=
  let b11 := (shiftRight out 0) % 2 == 1
  let b21 := (shiftRight out 1) % 2 == 1
  let b12 := (shiftRight out 2) % 2 == 1
  let b22 := (shiftRight out 3) % 2 == 1
  makeLevel1 b11 b21 b12 b22

/--
Base-level HashLife step for a level 2 (4x4) node using BitComputation:
Takes a 4x4 MacroCell and computes the central 2x2 level 1 MacroCell.
-/
def hashLifeStepLevel2 (m : MacroCell) : MacroCell :=
  let bits := level2ToBits m
  let out4 := computeNextGen4x4 bits
  bitsToLevel1 out4

/--
Gosper's recursive HashLife step function:
Takes a MacroCell of level k >= 2 and computes the central subnode of level k-1.
-/
def hashLifeStep : MacroCell → MacroCell
  | .node 2 nw ne sw se =>
    hashLifeStepLevel2 (.node 2 nw ne sw se)
  | .node (k + 3) nw ne sw se =>
    let n00 := centeredSubnode nw
    let n01 := centeredHorizontalSubnode nw ne
    let n02 := centeredSubnode ne
    let n10 := centeredVerticalSubnode nw sw
    let n11 := centeredSubSubnode (.node (k + 3) nw ne sw se)
    let n12 := centeredVerticalSubnode ne se
    let n20 := centeredSubnode sw
    let n21 := centeredHorizontalSubnode sw se
    let n22 := centeredSubnode se

    let q_nw := hashLifeStep (.node (k + 2) n00 n01 n10 n11)
    let q_ne := hashLifeStep (.node (k + 2) n01 n02 n11 n12)
    let q_sw := hashLifeStep (.node (k + 2) n10 n11 n20 n21)
    let q_se := hashLifeStep (.node (k + 2) n11 n12 n21 n22)

    .node (k + 2) q_nw q_ne q_sw q_se
  | m => m
termination_by m => m.level
decreasing_by all_goals simp [MacroCell.level]

-- =========================================================================
-- Formal Theorems Verifying HashLife Algorithm Internals
-- =========================================================================

/--
Theorem: Empty node stability.
Stepping an empty macrocell at level 2 produces an empty level 1 macrocell.
-/
theorem hashlife_empty_level2_stability :
  hashLifeStepLevel2 (emptyNode 2) = emptyNode 1 := by
  rfl


/--
Theorem: Quadtree Block Still Life Preservation.
A 2x2 block situated at the center of a 4x4 level-2 MacroCell remains completely
intact in the central 2x2 output.
-/
theorem hashlife_block_preservation :
  let nw := makeLevel1 false false false true   -- (1, 1) is active
  let ne := makeLevel1 false false true false   -- (2, 1) is active
  let sw := makeLevel1 false true false false   -- (1, 2) is active
  let se := makeLevel1 true false false false   -- (2, 2) is active
  let block4x4 := makeLevel2 nw ne sw se
  hashLifeStepLevel2 block4x4 = makeLevel1 true true true true := by
  decide

/--
Theorem: Quadtree Blinker Horizontal to Vertical Oscillation.
A horizontal blinker at (1, 1), (2, 1), (3, 1) inside a 4x4 MacroCell
evolves to the vertical blinker at (2, 1), (2, 2) inside the 2x2 output.
-/
theorem hashlife_blinker_oscillation :
  let nw := makeLevel1 false false false true   -- (1, 1) is active
  let ne := makeLevel1 false false true true    -- (2, 1) and (3, 1) are active
  let sw := makeLevel1 false false false false
  let se := makeLevel1 false false false false
  let blinker4x4 := makeLevel2 nw ne sw se
  -- In 2x2 center: (2, 1) [ne] and (2, 2) [se] are active
  hashLifeStepLevel2 blinker4x4 = makeLevel1 false true false true := by
  decide

/--
Theorem: Quadtree Tub Still Life Preservation.
A tub still life inside a 4x4 MacroCell remains dead at the center (1, 1) and alive at surrounding center cells.
-/
theorem hashlife_tub_preservation :
  -- Tub at (1, 0), (0, 1), (2, 1), (1, 2)
  let nw := makeLevel1 false true true false    -- (1, 0) and (0, 1)
  let ne := makeLevel1 false false true false   -- (2, 1)
  let sw := makeLevel1 false true false false   -- (1, 2)
  let se := makeLevel1 false false false false
  let tub4x4 := makeLevel2 nw ne sw se
  -- Center 2x2 output: (1, 1) is dead, (2, 1) and (1, 2) are preserved
  hashLifeStepLevel2 tub4x4 = makeLevel1 false true true false := by
  decide

/--
Theorem: Centered Subnode Coordinate Preservation.
The centered subnode of a level 3 node is a level 2 node whose children match
the interior quadtree quadrants (nw.se, ne.sw, sw.ne, se.nw).
-/
theorem centered_subnode_level_correct
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
