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

namespace Algorithm

def shiftRight (a : Nat) : Nat → Nat
  | 0 => a
  | k + 1 => shiftRight (a / 2) k

def testBit (w : Nat) (i : Nat) : Bool :=
  (shiftRight w i) % 2 == 1

def boolToNat (b : Bool) : Nat :=
  if b then 1 else 0

/--
Mapping from 4x4 bit index [0..15] to (x, y) coordinate.
Row 0: 0  1  4  5
Row 1: 2  3  6  7
Row 2: 8  9 12 13
Row 3: 10 11 14 15
-/
def bitToCoord4x4 : Nat → Option Coord
  | 0 => some (0, 0)
  | 1 => some (1, 0)
  | 2 => some (0, 1)
  | 3 => some (1, 1)
  | 4 => some (2, 0)
  | 5 => some (3, 0)
  | 6 => some (2, 1)
  | 7 => some (3, 1)
  | 8 => some (0, 2)
  | 9 => some (1, 2)
  | 10 => some (0, 3)
  | 11 => some (1, 3)
  | 12 => some (2, 2)
  | 13 => some (3, 2)
  | 14 => some (2, 3)
  | 15 => some (3, 3)
  | _ => none

/--
Converts 16-bit integer to list of active 2D coordinates.
-/
def natToGrid4x4 (w : Nat) : List Coord :=
  let indices := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  indices.filterMap fun i =>
    if testBit w i then bitToCoord4x4 i else none

/--
Count of alive neighbors for cell (2, 2) (bit 12):
Neighbor bit indices: 3, 6, 7, 9, 11, 13, 14, 15
-/
def neighborCount22 (w : Nat) : Nat :=
  boolToNat (testBit w 3) + boolToNat (testBit w 6) +
  boolToNat (testBit w 7) + boolToNat (testBit w 9) +
  boolToNat (testBit w 11) + boolToNat (testBit w 13) +
  boolToNat (testBit w 14) + boolToNat (testBit w 15)

/--
Count of alive neighbors for cell (1, 2) (bit 9):
Neighbor bit indices: 2, 3, 6, 8, 10, 11, 12, 14 (mask 0x5D4C)
-/
def neighborCount12 (w : Nat) : Nat :=
  boolToNat (testBit w 2) + boolToNat (testBit w 3) +
  boolToNat (testBit w 6) + boolToNat (testBit w 8) +
  boolToNat (testBit w 10) + boolToNat (testBit w 11) +
  boolToNat (testBit w 12) + boolToNat (testBit w 14)

/--
Count of alive neighbors for cell (2, 1) (bit 6):
Neighbor bit indices: 1, 3, 4, 5, 7, 9, 12, 13 (mask 0x32BA)
-/
def neighborCount21 (w : Nat) : Nat :=
  boolToNat (testBit w 1) + boolToNat (testBit w 3) +
  boolToNat (testBit w 4) + boolToNat (testBit w 5) +
  boolToNat (testBit w 7) + boolToNat (testBit w 9) +
  boolToNat (testBit w 12) + boolToNat (testBit w 13)

/--
Count of alive neighbors for cell (1, 1) (bit 3):
Neighbor bit indices: 0, 1, 2, 4, 6, 8, 9, 12
-/
def neighborCount11 (w : Nat) : Nat :=
  boolToNat (testBit w 0) + boolToNat (testBit w 1) +
  boolToNat (testBit w 2) + boolToNat (testBit w 4) +
  boolToNat (testBit w 6) + boolToNat (testBit w 8) +
  boolToNat (testBit w 9) + boolToNat (testBit w 12)

/--
Conway rule as computed in BitComputation:
`(count or prevBit) ^ 3 == 0`
-/
def bitRule (count : Nat) (prevBit : Bool) : Bool :=
  let p := if prevBit then 1 else 0
  -- In Conway: alive iff count == 3 || (count == 2 && prevBit)
  count == 3 || (count == 2 && p == 1)

/--
Computes next generation center 2x2 of 4x4 grid as a 4-bit integer:
  bit 3: cell (2, 2)
  bit 2: cell (1, 2)
  bit 1: cell (2, 1)
  bit 0: cell (1, 1)
-/
def computeNextGen4x4 (w : Nat) : Nat :=
  let b22 := bitRule (neighborCount22 w) (testBit w 12)
  let b12 := bitRule (neighborCount12 w) (testBit w 9)
  let b21 := bitRule (neighborCount21 w) (testBit w 6)
  let b11 := bitRule (neighborCount11 w) (testBit w 3)
  boolToNat b22 * 8 + boolToNat b12 * 4 + boolToNat b21 * 2 + boolToNat b11

def centerBitsToCoords (out : Nat) : List Coord :=
  let b0 := testBit out 0
  let b1 := testBit out 1
  let b2 := testBit out 2
  let b3 := testBit out 3
  (if b0 then [(1, 1)] else []) ++
  (if b1 then [(2, 1)] else []) ++
  (if b2 then [(1, 2)] else []) ++
  (if b3 then [(2, 2)] else [])

/--
Computes center 2x2 cells using Naive Moore stepping on the 4x4 grid.
-/
def naiveCenter2x2 (w : Nat) : List Coord :=
  let grid := natToGrid4x4 w
  let nextGrid := stepGrid grid
  nextGrid.filter fun (x, y) =>
    (x == 1 || x == 2) && (y == 1 || y == 2)

def verifyBitComputation4x4 (w : Nat) : Bool :=
  let bitCenter := centerBitsToCoords (computeNextGen4x4 w)
  let naiveCenter := naiveCenter2x2 w
  bitCenter.all (naiveCenter.contains ·) && naiveCenter.all (bitCenter.contains ·)

-- Formal verification theorems:
theorem bit_comp_empty_correct :
  verifyBitComputation4x4 0 = true := by
  decide

theorem bit_comp_blinker_h_correct :
  -- Blinker horizontal at (1, 1), (2, 1), (3, 1): bits 3, 6, 7
  verifyBitComputation4x4 (2^3 + 2^6 + 2^7) = true := by
  decide

theorem bit_comp_blinker_v_correct :
  -- Blinker vertical at (1, 0), (1, 1), (1, 2): bits 1, 3, 9
  verifyBitComputation4x4 (2^1 + 2^3 + 2^9) = true := by
  decide

theorem bit_comp_block_correct :
  -- Block at (1, 1), (2, 1), (1, 2), (2, 2): bits 3, 6, 9, 12
  verifyBitComputation4x4 (2^3 + 2^6 + 2^9 + 2^12) = true := by
  decide

theorem bit_comp_glider_sub_correct :
  -- Glider subpattern at (1, 0), (2, 1), (0, 2), (1, 2), (2, 2): bits 1, 6, 8, 9, 12
  verifyBitComputation4x4 (2^1 + 2^6 + 2^8 + 2^9 + 2^12) = true := by
  decide

theorem bit_comp_tub_correct :
  -- Tub at (1, 0), (0, 1), (2, 1), (1, 2): bits 1, 2, 6, 9
  verifyBitComputation4x4 (2^1 + 2^2 + 2^6 + 2^9) = true := by
  decide

-- =========================================================================
-- 8x8 LeafNode Computation (MacroCell.LeafNode.computeNextGeneration)
-- =========================================================================

/--
Extracts a 2x2 subnode (4 bits) from four bit positions of a 64-bit leaf node.
-/
def extractSub2x2 (w : Nat) (b0 b1 b2 b3 : Nat) : Nat :=
  boolToNat (testBit w b0) +
  boolToNat (testBit w b1) * 2 +
  boolToNat (testBit w b2) * 4 +
  boolToNat (testBit w b3) * 8

/--
Computes the central 4x4 next generation for an 8x8 64-bit MacroCell.LeafNode.
Implements the 9-subnode decomposition (n00..n22) into four 4x4 quadrant evaluations.
-/
def computeLeafNextGen8x8 (w : Nat) : Nat :=
  let n00 := extractSub2x2 w 0x03 0x06 0x09 0x0C
  let n01 := extractSub2x2 w 0x07 0x12 0x0D 0x18
  let n02 := extractSub2x2 w 0x13 0x16 0x19 0x1C
  let n10 := extractSub2x2 w 0x0B 0x0E 0x21 0x24
  let n11 := extractSub2x2 w 0x0F 0x1A 0x25 0x30
  let n12 := extractSub2x2 w 0x1B 0x1E 0x31 0x34
  let n20 := extractSub2x2 w 0x23 0x26 0x29 0x2C
  let n21 := extractSub2x2 w 0x27 0x32 0x2D 0x38
  let n22 := extractSub2x2 w 0x33 0x36 0x39 0x3C

  let nw := computeNextGen4x4 (n00 + n01 * 16 + n10 * 256 + n11 * 4096)
  let ne := computeNextGen4x4 (n01 + n02 * 16 + n11 * 256 + n12 * 4096)
  let sw := computeNextGen4x4 (n10 + n11 * 16 + n20 * 256 + n21 * 4096)
  let se := computeNextGen4x4 (n11 + n12 * 16 + n21 * 256 + n22 * 4096)

  nw + ne * 16 + sw * 256 + se * 4096

/--
Maps an 8x8 bit index [0..63] to 2D coordinate (x, y).
-/
def bitToCoord8x8 (b : Nat) : Option Coord :=
  if b >= 64 then none
  else
    let quad := b / 16
    let localBit := b % 16
    match bitToCoord4x4 localBit with
    | none => none
    | some (lx, ly) =>
      let (ox, oy) : Coord := match quad with
        | 0 => (0, 0)
        | 1 => (4, 0)
        | 2 => (0, 4)
        | _ => (4, 4)
      some (lx + ox, ly + oy)

def leafBitsToCoords (w : Nat) : List Coord :=
  (List.range 64).filterMap (fun b =>
    if testBit w b then bitToCoord8x8 b else none
  )

def center4x4BitsToCoords (out16 : Nat) : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit out16 b then
      match bitToCoord4x4 b with
      | none => none
      | some (x, y) => some (x + 2, y + 2)
    else none
  )

def naiveCenter4x4 (w : Nat) : List Coord :=
  let fullGrid := leafBitsToCoords w
  let nextGrid := stepGrid fullGrid
  nextGrid.filter (fun (x, y) => x >= 2 && x <= 5 && y >= 2 && y <= 5)

def verifyLeafComputation8x8 (w : Nat) : Bool :=
  let bitCenter := center4x4BitsToCoords (computeLeafNextGen8x8 w)
  let naiveCenter := naiveCenter4x4 w
  bitCenter.all (naiveCenter.contains ·) && naiveCenter.all (bitCenter.contains ·)

-- Formal verification theorems for 8x8 LeafNode computation:
theorem leaf_comp_empty_correct :
  verifyLeafComputation8x8 0 = true := by
  decide

theorem leaf_comp_centered_block_correct :
  -- Block centered at (3,3), (4,3), (3,4), (4,4): bits 0x0F, 0x1A, 0x25, 0x30
  verifyLeafComputation8x8 (2^0x0F + 2^0x1A + 2^0x25 + 2^0x30) = true := by
  decide

theorem leaf_comp_centered_blinker_h_correct :
  -- Horizontal blinker at (2, 3), (3, 3), (4, 3):
  -- (2, 3) is bit 0x0E (14)
  -- (3, 3) is bit 0x0F (15)
  -- (4, 3) is bit 0x1A (26)
  verifyLeafComputation8x8 (2^0x0E + 2^0x0F + 2^0x1A) = true := by
  decide

theorem leaf_comp_centered_tub_correct :
  -- Tub at (3, 2), (2, 3), (4, 3), (3, 4):
  -- (3, 2) is bit 0x0D (13)
  -- (2, 3) is bit 0x0E (14)
  -- (4, 3) is bit 0x1A (26)
  -- (3, 4) is bit 0x25 (37)
  verifyLeafComputation8x8 (2^0x0D + 2^0x0E + 2^0x1A + 2^0x25) = true := by
  decide

-- =========================================================================
-- Universal Correctness: Proof by Neighborhood Soundness and Completeness
-- =========================================================================

/--
Theorem: bitRule is definitionally identical to Conway's lifeRule for all neighbor counts and states.
-/
theorem bitRule_equals_lifeRule (alive : Bool) (n : Nat) :
  bitRule n alive = lifeRule alive n := by
  cases alive <;> rfl

def mask11Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0x1357 b then bitToCoord4x4 b else none
  )

def mask21Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0x32BA b then bitToCoord4x4 b else none
  )

def mask12Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0x5D4C b then bitToCoord4x4 b else none
  )

def mask22Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0xEAC8 b then bitToCoord4x4 b else none
  )

/--
Theorem: Mask 0x1357 covers the exact Moore neighborhood of (1, 1) in the 4x4 grid.
-/
theorem mask11_is_exact_moore_neighborhood :
  mask11Neighbors.all (mooreNeighbors (1, 1)).contains ∧
  (mooreNeighbors (1, 1)).all mask11Neighbors.contains ∧
  mask11Neighbors.length = 8 := by
  decide

/--
Theorem: Mask 0x32BA covers the exact Moore neighborhood of (2, 1) in the 4x4 grid.
-/
theorem mask21_is_exact_moore_neighborhood :
  mask21Neighbors.all (mooreNeighbors (2, 1)).contains ∧
  (mooreNeighbors (2, 1)).all mask21Neighbors.contains ∧
  mask21Neighbors.length = 8 := by
  decide

/--
Theorem: Mask 0x5D4C covers the exact Moore neighborhood of (1, 2) in the 4x4 grid.
-/
theorem mask12_is_exact_moore_neighborhood :
  mask12Neighbors.all (mooreNeighbors (1, 2)).contains ∧
  (mooreNeighbors (1, 2)).all mask12Neighbors.contains ∧
  mask12Neighbors.length = 8 := by
  decide

/--
Theorem: Mask 0xEAC8 covers the exact Moore neighborhood of (2, 2) in the 4x4 grid.
-/
theorem mask22_is_exact_moore_neighborhood :
  mask22Neighbors.all (mooreNeighbors (2, 2)).contains ∧
  (mooreNeighbors (2, 2)).all mask22Neighbors.contains ∧
  mask22Neighbors.length = 8 := by
  decide

-- 8x8 Quadrant Moore Neighborhood Containment Theorems:

def nwQuadrantBits : List Nat :=
  [0x03, 0x06, 0x09, 0x0C, 0x07, 0x12, 0x0D, 0x18,
   0x0B, 0x0E, 0x21, 0x24, 0x0F, 0x1A, 0x25, 0x30]

def neQuadrantBits : List Nat :=
  [0x07, 0x12, 0x0D, 0x18, 0x13, 0x16, 0x19, 0x1C,
   0x0F, 0x1A, 0x25, 0x30, 0x1B, 0x1E, 0x31, 0x34]

def swQuadrantBits : List Nat :=
  [0x0B, 0x0E, 0x21, 0x24, 0x0F, 0x1A, 0x25, 0x30,
   0x23, 0x26, 0x29, 0x2C, 0x27, 0x32, 0x2D, 0x38]

def seQuadrantBits : List Nat :=
  [0x0F, 0x1A, 0x25, 0x30, 0x1B, 0x1E, 0x31, 0x34,
   0x27, 0x32, 0x2D, 0x38, 0x33, 0x36, 0x39, 0x3C]

def nwQuadrantCoords : List Coord :=
  nwQuadrantBits.filterMap bitToCoord8x8

def neQuadrantCoords : List Coord :=
  neQuadrantBits.filterMap bitToCoord8x8

def swQuadrantCoords : List Coord :=
  swQuadrantBits.filterMap bitToCoord8x8

def seQuadrantCoords : List Coord :=
  seQuadrantBits.filterMap bitToCoord8x8

/--
Theorem: For every cell in the NW center 2x2 of the 8x8 grid, all 8 Moore neighbors
are strictly contained within the NW quadrant input block.
-/
theorem nw_quadrant_contains_all_moore_neighbors :
  let centerNW : List Coord := [(2, 2), (3, 2), (2, 3), (3, 3)]
  centerNW.all (fun c => (mooreNeighbors c).all nwQuadrantCoords.contains) = true := by
  decide

/--
Theorem: For every cell in the NE center 2x2 of the 8x8 grid, all 8 Moore neighbors
are strictly contained within the NE quadrant input block.
-/
theorem ne_quadrant_contains_all_moore_neighbors :
  let centerNE : List Coord := [(4, 2), (5, 2), (4, 3), (5, 3)]
  centerNE.all (fun c => (mooreNeighbors c).all neQuadrantCoords.contains) = true := by
  decide

/--
Theorem: For every cell in the SW center 2x2 of the 8x8 grid, all 8 Moore neighbors
are strictly contained within the SW quadrant input block.
-/
theorem sw_quadrant_contains_all_moore_neighbors :
  let centerSW : List Coord := [(2, 4), (3, 4), (2, 5), (3, 5)]
  centerSW.all (fun c => (mooreNeighbors c).all swQuadrantCoords.contains) = true := by
  decide

/--
Theorem: For every cell in the SE center 2x2 of the 8x8 grid, all 8 Moore neighbors
are strictly contained within the SE quadrant input block.
-/
theorem se_quadrant_contains_all_moore_neighbors :
  let centerSE : List Coord := [(4, 4), (5, 4), (4, 5), (5, 5)]
  centerSE.all (fun c => (mooreNeighbors c).all seQuadrantCoords.contains) = true := by
  decide

-- =========================================================================
-- Optimized 8x8 Computation and Equivalence Proof
-- =========================================================================

def extractCenter (q : Nat) : Nat :=
  boolToNat (testBit q 3) +
  boolToNat (testBit q 6) * 2 +
  boolToNat (testBit q 9) * 4 +
  boolToNat (testBit q 12) * 8

def extractHorizontalMid (leftQuad rightQuad : Nat) : Nat :=
  boolToNat (testBit leftQuad 7) +
  boolToNat (testBit rightQuad 2) * 2 +
  boolToNat (testBit leftQuad 13) * 4 +
  boolToNat (testBit rightQuad 8) * 8

def extractVerticalMid (topQuad bottomQuad : Nat) : Nat :=
  boolToNat (testBit topQuad 11) +
  boolToNat (testBit topQuad 14) * 2 +
  boolToNat (testBit bottomQuad 1) * 4 +
  boolToNat (testBit bottomQuad 4) * 8

def extractCenterMid (q0 q1 q2 q3 : Nat) : Nat :=
  boolToNat (testBit q0 15) +
  boolToNat (testBit q1 10) * 2 +
  boolToNat (testBit q2 5) * 4 +
  boolToNat (testBit q3 0) * 8

def quad0 (w : Nat) : Nat := shiftRight w 0
def quad1 (w : Nat) : Nat := shiftRight w 16
def quad2 (w : Nat) : Nat := shiftRight w 32
def quad3 (w : Nat) : Nat := shiftRight w 48

/--
Optimized 8x8 next generation computation reflecting the 32-bit quadrant decomposed implementation.
-/
def computeLeafNextGen8x8Fast (w : Nat) : Nat :=
  let q0 := quad0 w
  let q1 := quad1 w
  let q2 := quad2 w
  let q3 := quad3 w

  let n00 := extractCenter q0
  let n02 := extractCenter q1
  let n20 := extractCenter q2
  let n22 := extractCenter q3

  let n01 := extractHorizontalMid q0 q1
  let n21 := extractHorizontalMid q2 q3

  let n10 := extractVerticalMid q0 q2
  let n12 := extractVerticalMid q1 q3

  let n11 := extractCenterMid q0 q1 q2 q3

  let nw := computeNextGen4x4 (n00 + n01 * 16 + n10 * 256 + n11 * 4096)
  let ne := computeNextGen4x4 (n01 + n02 * 16 + n11 * 256 + n12 * 4096)
  let sw := computeNextGen4x4 (n10 + n11 * 16 + n20 * 256 + n21 * 4096)
  let se := computeNextGen4x4 (n11 + n12 * 16 + n21 * 256 + n22 * 4096)

  nw + ne * 16 + sw * 256 + se * 4096

/--
Theorem: The optimized computeLeafNextGen8x8Fast is definitionally equivalent
to computeLeafNextGen8x8 for ALL inputs w.
-/
theorem computeLeafNextGen8x8Fast_eq_computeLeafNextGen8x8 (w : Nat) :
  computeLeafNextGen8x8Fast w = computeLeafNextGen8x8 w := by
  rfl

/--
Branching 8x8 computation with 0-short-circuiting matching Kotlin's fast path.
-/
def computeLeafNextGen8x8Branch (w : Nat) : Nat :=
  if w == 0 then 0 else computeLeafNextGen8x8Fast w

/--
Theorem: For input 0 (empty leaf), computeLeafNextGen8x8Fast evaluates to 0.
-/
theorem computeLeafNextGen8x8Fast_zero : computeLeafNextGen8x8Fast 0 = 0 := by
  rfl

/--
Theorem: The branching fast-path implementation is mathematically equivalent
to computeLeafNextGen8x8 for ALL inputs w.
-/
theorem computeLeafNextGen8x8Branch_eq_computeLeafNextGen8x8 (w : Nat) :
  computeLeafNextGen8x8Branch w = computeLeafNextGen8x8 w := by
  unfold computeLeafNextGen8x8Branch
  split
  · rename_i h
    have heq : w = 0 := of_decide_eq_true h
    rw [heq]
    rfl
  · exact computeLeafNextGen8x8Fast_eq_computeLeafNextGen8x8 w

end Algorithm
