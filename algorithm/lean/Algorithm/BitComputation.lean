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

local notation "ℕ" => Nat

namespace Algorithm

def shiftRight (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k + 1 => shiftRight (a / 2) k

def testBit (w : ℕ) (i : ℕ) : Bool :=
  (shiftRight w i) % 2 == 1

def boolToNat (b : Bool) : ℕ :=
  if b then 1 else 0

/--
Mapping from 4x4 bit index [0..15] to (x, y) coordinate.
Row 0: 0  1  4  5
Row 1: 2  3  6  7
Row 2: 8  9 12 13
Row 3: 10 11 14 15
-/
def bitToCoord4x4 : ℕ → Option Coord
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
def natToGrid4x4 (w : ℕ) : List Coord :=
  let indices := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  indices.filterMap fun i =>
    if testBit w i then bitToCoord4x4 i else none

/--
Count of alive neighbors for cell (2, 2) (bit 12):
Neighbor bit indices: 3, 6, 7, 9, 11, 13, 14, 15
-/
def neighborCount22 (w : ℕ) : ℕ :=
  boolToNat (testBit w 3) + boolToNat (testBit w 6) +
  boolToNat (testBit w 7) + boolToNat (testBit w 9) +
  boolToNat (testBit w 11) + boolToNat (testBit w 13) +
  boolToNat (testBit w 14) + boolToNat (testBit w 15)

/--
Count of alive neighbors for cell (1, 2) (bit 9):
Neighbor bit indices: 2, 3, 6, 8, 10, 11, 12, 14 (mask 0x5D4C)
-/
def neighborCount12 (w : ℕ) : ℕ :=
  boolToNat (testBit w 2) + boolToNat (testBit w 3) +
  boolToNat (testBit w 6) + boolToNat (testBit w 8) +
  boolToNat (testBit w 10) + boolToNat (testBit w 11) +
  boolToNat (testBit w 12) + boolToNat (testBit w 14)

/--
Count of alive neighbors for cell (2, 1) (bit 6):
Neighbor bit indices: 1, 3, 4, 5, 7, 9, 12, 13 (mask 0x32BA)
-/
def neighborCount21 (w : ℕ) : ℕ :=
  boolToNat (testBit w 1) + boolToNat (testBit w 3) +
  boolToNat (testBit w 4) + boolToNat (testBit w 5) +
  boolToNat (testBit w 7) + boolToNat (testBit w 9) +
  boolToNat (testBit w 12) + boolToNat (testBit w 13)

/--
Count of alive neighbors for cell (1, 1) (bit 3):
Neighbor bit indices: 0, 1, 2, 4, 6, 8, 9, 12
-/
def neighborCount11 (w : ℕ) : ℕ :=
  boolToNat (testBit w 0) + boolToNat (testBit w 1) +
  boolToNat (testBit w 2) + boolToNat (testBit w 4) +
  boolToNat (testBit w 6) + boolToNat (testBit w 8) +
  boolToNat (testBit w 9) + boolToNat (testBit w 12)

/--
Conway rule as computed in BitComputation:
`(count or prevBit) ^ 3 == 0`
-/
def bitRule (count : ℕ) (prevBit : Bool) : Bool :=
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
def computeNextGen4x4 (w : ℕ) : ℕ :=
  let b22 := bitRule (neighborCount22 w) (testBit w 12)
  let b12 := bitRule (neighborCount12 w) (testBit w 9)
  let b21 := bitRule (neighborCount21 w) (testBit w 6)
  let b11 := bitRule (neighborCount11 w) (testBit w 3)
  boolToNat b22 * 8 + boolToNat b12 * 4 + boolToNat b21 * 2 + boolToNat b11

def centerBitsToCoords (out : ℕ) : List Coord :=
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
def naiveCenter2x2 (w : ℕ) : List Coord :=
  let grid := natToGrid4x4 w
  let nextGrid := stepGrid grid
  nextGrid.filter fun (x, y) =>
    (x == 1 || x == 2) && (y == 1 || y == 2)

def verifyBitComputation4x4 (w : ℕ) : Bool :=
  let bitCenter := centerBitsToCoords (computeNextGen4x4 w)
  let naiveCenter := naiveCenter2x2 w
  bitCenter.all (naiveCenter.contains ·) && naiveCenter.all (bitCenter.contains ·)


-- =========================================================================
-- 8x8 LeafNode Computation (MacroCell.LeafNode.computeNextGeneration)
-- =========================================================================

/--
Extracts a 2x2 subnode (4 bits) from four bit positions of a 64-bit leaf node.
-/
def extractSub2x2 (w : ℕ) (b0 b1 b2 b3 : ℕ) : ℕ :=
  boolToNat (testBit w b0) +
  boolToNat (testBit w b1) * 2 +
  boolToNat (testBit w b2) * 4 +
  boolToNat (testBit w b3) * 8

/--
Computes the central 4x4 next generation for an 8x8 64-bit MacroCell.LeafNode.
Implements the 9-subnode decomposition (n00..n22) into four 4x4 quadrant evaluations.
-/
def computeLeafNextGen8x8 (w : ℕ) : ℕ :=
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
def bitToCoord8x8 (b : ℕ) : Option Coord :=
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

def leafBitsToCoords (w : ℕ) : List Coord :=
  (List.range 64).filterMap (fun b =>
    if testBit w b then bitToCoord8x8 b else none
  )

def center4x4BitsToCoords (out16 : ℕ) : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit out16 b then
      match bitToCoord4x4 b with
      | none => none
      | some (x, y) => some (x + 2, y + 2)
    else none
  )

def naiveCenter4x4 (w : ℕ) : List Coord :=
  let fullGrid := leafBitsToCoords w
  let nextGrid := stepGrid fullGrid
  nextGrid.filter (fun (x, y) => x >= 2 && x <= 5 && y >= 2 && y <= 5)

def verifyLeafComputation8x8 (w : ℕ) : Bool :=
  let bitCenter := center4x4BitsToCoords (computeLeafNextGen8x8 w)
  let naiveCenter := naiveCenter4x4 w
  bitCenter.all (naiveCenter.contains ·) && naiveCenter.all (bitCenter.contains ·)


-- =========================================================================
-- Optimized 8x8 Computation and Equivalence Proof
-- =========================================================================

def extractCenter (q : ℕ) : ℕ :=
  boolToNat (testBit q 3) +
  boolToNat (testBit q 6) * 2 +
  boolToNat (testBit q 9) * 4 +
  boolToNat (testBit q 12) * 8

def extractHorizontalMid (leftQuad rightQuad : ℕ) : ℕ :=
  boolToNat (testBit leftQuad 7) +
  boolToNat (testBit rightQuad 2) * 2 +
  boolToNat (testBit leftQuad 13) * 4 +
  boolToNat (testBit rightQuad 8) * 8

def extractVerticalMid (topQuad bottomQuad : ℕ) : ℕ :=
  boolToNat (testBit topQuad 11) +
  boolToNat (testBit topQuad 14) * 2 +
  boolToNat (testBit bottomQuad 1) * 4 +
  boolToNat (testBit bottomQuad 4) * 8

def extractCenterMid (q0 q1 q2 q3 : ℕ) : ℕ :=
  boolToNat (testBit q0 15) +
  boolToNat (testBit q1 10) * 2 +
  boolToNat (testBit q2 5) * 4 +
  boolToNat (testBit q3 0) * 8

def quad0 (w : ℕ) : ℕ := shiftRight w 0
def quad1 (w : ℕ) : ℕ := shiftRight w 16
def quad2 (w : ℕ) : ℕ := shiftRight w 32
def quad3 (w : ℕ) : ℕ := shiftRight w 48

/--
Optimized 8x8 next generation computation reflecting the 32-bit quadrant decomposed implementation.
-/
def computeLeafNextGen8x8Fast (w : ℕ) : ℕ :=
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
Branching 8x8 computation with 0-short-circuiting matching Kotlin's fast path.
-/
def computeLeafNextGen8x8Branch (w : ℕ) : ℕ :=
  if w == 0 then 0 else computeLeafNextGen8x8Fast w

-- =========================================================================
-- Fixed-width UInt32 / UInt64 Bit Computations for Production Kotlin Codegen
-- =========================================================================

def neighborCount22UInt (w : UInt32) : UInt32 :=
  ((w >>> 3) &&& (1 : UInt32)) + ((w >>> 6) &&& (1 : UInt32)) +
  ((w >>> 7) &&& (1 : UInt32)) + ((w >>> 9) &&& (1 : UInt32)) +
  ((w >>> 11) &&& (1 : UInt32)) + ((w >>> 13) &&& (1 : UInt32)) +
  ((w >>> 14) &&& (1 : UInt32)) + ((w >>> 15) &&& (1 : UInt32))

def neighborCount12UInt (w : UInt32) : UInt32 :=
  ((w >>> 2) &&& (1 : UInt32)) + ((w >>> 3) &&& (1 : UInt32)) +
  ((w >>> 6) &&& (1 : UInt32)) + ((w >>> 8) &&& (1 : UInt32)) +
  ((w >>> 10) &&& (1 : UInt32)) + ((w >>> 11) &&& (1 : UInt32)) +
  ((w >>> 12) &&& (1 : UInt32)) + ((w >>> 14) &&& (1 : UInt32))

def neighborCount21UInt (w : UInt32) : UInt32 :=
  ((w >>> 1) &&& (1 : UInt32)) + ((w >>> 3) &&& (1 : UInt32)) +
  ((w >>> 4) &&& (1 : UInt32)) + ((w >>> 5) &&& (1 : UInt32)) +
  ((w >>> 7) &&& (1 : UInt32)) + ((w >>> 9) &&& (1 : UInt32)) +
  ((w >>> 12) &&& (1 : UInt32)) + ((w >>> 13) &&& (1 : UInt32))

def neighborCount11UInt (w : UInt32) : UInt32 :=
  ((w >>> 0) &&& (1 : UInt32)) + ((w >>> 1) &&& (1 : UInt32)) +
  ((w >>> 2) &&& (1 : UInt32)) + ((w >>> 4) &&& (1 : UInt32)) +
  ((w >>> 6) &&& (1 : UInt32)) + ((w >>> 8) &&& (1 : UInt32)) +
  ((w >>> 9) &&& (1 : UInt32)) + ((w >>> 12) &&& (1 : UInt32))

def bitRuleUInt (count : UInt32) (prevBit : UInt32) : UInt32 :=
  if count == 3 || (count == 2 && prevBit == (1 : UInt32)) then 1 else 0

@[export computeNextGen4x4UInt]
def computeNextGen4x4UInt (w : UInt32) : UInt32 :=
  let b22 := bitRuleUInt (neighborCount22UInt w) ((w >>> 12) &&& (1 : UInt32))
  let b12 := bitRuleUInt (neighborCount12UInt w) ((w >>> 9) &&& (1 : UInt32))
  let b21 := bitRuleUInt (neighborCount21UInt w) ((w >>> 6) &&& (1 : UInt32))
  let b11 := bitRuleUInt (neighborCount11UInt w) ((w >>> 3) &&& (1 : UInt32))
  (b22 <<< 3) ||| (b12 <<< 2) ||| (b21 <<< 1) ||| b11

def extractCenterUInt (q : UInt32) : UInt32 :=
  ((q >>> 3) &&& (1 : UInt32)) |||
  (((q >>> 6) &&& (1 : UInt32)) <<< 1) |||
  (((q >>> 9) &&& (1 : UInt32)) <<< 2) |||
  (((q >>> 12) &&& (1 : UInt32)) <<< 3)

def extractHorizontalMidUInt (leftQuad rightQuad : UInt32) : UInt32 :=
  ((leftQuad >>> 7) &&& (1 : UInt32)) |||
  (((rightQuad >>> 2) &&& (1 : UInt32)) <<< 1) |||
  (((leftQuad >>> 13) &&& (1 : UInt32)) <<< 2) |||
  (((rightQuad >>> 8) &&& (1 : UInt32)) <<< 3)

def extractVerticalMidUInt (topQuad bottomQuad : UInt32) : UInt32 :=
  ((topQuad >>> 11) &&& (1 : UInt32)) |||
  (((topQuad >>> 14) &&& (1 : UInt32)) <<< 1) |||
  (((bottomQuad >>> 1) &&& (1 : UInt32)) <<< 2) |||
  (((bottomQuad >>> 4) &&& (1 : UInt32)) <<< 3)

def extractCenterMidUInt (q0 q1 q2 q3 : UInt32) : UInt32 :=
  ((q0 >>> 15) &&& (1 : UInt32)) |||
  (((q1 >>> 10) &&& (1 : UInt32)) <<< 1) |||
  (((q2 >>> 5) &&& (1 : UInt32)) <<< 2) |||
  (((q3 >>> 0) &&& (1 : UInt32)) <<< 3)

def quad0UInt (w : UInt64) : UInt32 := (w &&& (0xFFFF : UInt64)).toUInt32
def quad1UInt (w : UInt64) : UInt32 := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
def quad2UInt (w : UInt64) : UInt32 := ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
def quad3UInt (w : UInt64) : UInt32 := ((w >>> 48) &&& (0xFFFF : UInt64)).toUInt32

def computeLeafNextGen8x8FastUInt (w : UInt64) : UInt32 :=
  let q0 := quad0UInt w
  let q1 := quad1UInt w
  let q2 := quad2UInt w
  let q3 := quad3UInt w

  let n00 := extractCenterUInt q0
  let n02 := extractCenterUInt q1
  let n20 := extractCenterUInt q2
  let n22 := extractCenterUInt q3

  let n01 := extractHorizontalMidUInt q0 q1
  let n21 := extractHorizontalMidUInt q2 q3

  let n10 := extractVerticalMidUInt q0 q2
  let n12 := extractVerticalMidUInt q1 q3

  let n11 := extractCenterMidUInt q0 q1 q2 q3

  let nw := computeNextGen4x4UInt (n00 ||| (n01 <<< 4) ||| (n10 <<< 8) ||| (n11 <<< 12))
  let ne := computeNextGen4x4UInt (n01 ||| (n02 <<< 4) ||| (n11 <<< 8) ||| (n12 <<< 12))
  let sw := computeNextGen4x4UInt (n10 ||| (n11 <<< 4) ||| (n20 <<< 8) ||| (n21 <<< 12))
  let se := computeNextGen4x4UInt (n11 ||| (n12 <<< 4) ||| (n21 <<< 8) ||| (n22 <<< 12))

  nw ||| (ne <<< 4) ||| (sw <<< 8) ||| (se <<< 12)

@[export computeLeafNextGen8x8BranchUInt]
def computeLeafNextGen8x8BranchUInt (w : UInt64) : UInt32 :=
  if w == 0 then 0 else computeLeafNextGen8x8FastUInt w

def verifyBitComputation4x4UInt (w : UInt32) : Bool :=
  let bitCenter := centerBitsToCoords (computeNextGen4x4UInt w).toNat
  let naiveCenter := naiveCenter2x2 w.toNat
  bitCenter.all (naiveCenter.contains ·) && naiveCenter.all (bitCenter.contains ·)

def verifyLeafComputation8x8UInt (w : UInt64) : Bool :=
  let bitCenter := center4x4BitsToCoords (computeLeafNextGen8x8BranchUInt w).toNat
  let naiveCenter := naiveCenter4x4 w.toNat
  bitCenter.all (naiveCenter.contains ·) && naiveCenter.all (bitCenter.contains ·)

end Algorithm

