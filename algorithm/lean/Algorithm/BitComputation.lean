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

end Algorithm
