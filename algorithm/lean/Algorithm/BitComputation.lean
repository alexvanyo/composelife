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
import Lean.Compiler.Kotlin

open Lean.Compiler.Kotlin

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

-- =========================================================================
-- Fixed-width UInt32 / UInt64 Bit Computations for Production Kotlin Codegen
-- =========================================================================

@[inline]
def neighborCount22UInt (w : UInt32) : UInt32 :=
  ((w >>> 3) &&& (1 : UInt32)) + ((w >>> 6) &&& (1 : UInt32)) +
  ((w >>> 7) &&& (1 : UInt32)) + ((w >>> 9) &&& (1 : UInt32)) +
  ((w >>> 11) &&& (1 : UInt32)) + ((w >>> 13) &&& (1 : UInt32)) +
  ((w >>> 14) &&& (1 : UInt32)) + ((w >>> 15) &&& (1 : UInt32))

@[inline]
def neighborCount12UInt (w : UInt32) : UInt32 :=
  ((w >>> 2) &&& (1 : UInt32)) + ((w >>> 3) &&& (1 : UInt32)) +
  ((w >>> 6) &&& (1 : UInt32)) + ((w >>> 8) &&& (1 : UInt32)) +
  ((w >>> 10) &&& (1 : UInt32)) + ((w >>> 11) &&& (1 : UInt32)) +
  ((w >>> 12) &&& (1 : UInt32)) + ((w >>> 14) &&& (1 : UInt32))

@[inline]
def neighborCount21UInt (w : UInt32) : UInt32 :=
  ((w >>> 1) &&& (1 : UInt32)) + ((w >>> 3) &&& (1 : UInt32)) +
  ((w >>> 4) &&& (1 : UInt32)) + ((w >>> 5) &&& (1 : UInt32)) +
  ((w >>> 7) &&& (1 : UInt32)) + ((w >>> 9) &&& (1 : UInt32)) +
  ((w >>> 12) &&& (1 : UInt32)) + ((w >>> 13) &&& (1 : UInt32))

@[inline]
def neighborCount11UInt (w : UInt32) : UInt32 :=
  ((w >>> 0) &&& (1 : UInt32)) + ((w >>> 1) &&& (1 : UInt32)) +
  ((w >>> 2) &&& (1 : UInt32)) + ((w >>> 4) &&& (1 : UInt32)) +
  ((w >>> 6) &&& (1 : UInt32)) + ((w >>> 8) &&& (1 : UInt32)) +
  ((w >>> 9) &&& (1 : UInt32)) + ((w >>> 12) &&& (1 : UInt32))

@[inline]
def bitRuleUInt (count : UInt32) (prevBit : UInt32) : UInt32 :=
  if count == 3 || (count == 2 && prevBit == (1 : UInt32)) then 1 else 0

@[inline]
def extractCenterUInt (q : UInt32) : UInt32 :=
  ((q >>> 3) &&& (1 : UInt32)) |||
  (((q >>> 6) &&& (1 : UInt32)) <<< 1) |||
  (((q >>> 9) &&& (1 : UInt32)) <<< 2) |||
  (((q >>> 12) &&& (1 : UInt32)) <<< 3)

@[inline]
def extractHorizontalMidUInt (leftQuad rightQuad : UInt32) : UInt32 :=
  ((leftQuad >>> 7) &&& (1 : UInt32)) |||
  (((rightQuad >>> 2) &&& (1 : UInt32)) <<< 1) |||
  (((leftQuad >>> 13) &&& (1 : UInt32)) <<< 2) |||
  (((rightQuad >>> 8) &&& (1 : UInt32)) <<< 3)

@[inline]
def extractVerticalMidUInt (topQuad bottomQuad : UInt32) : UInt32 :=
  ((topQuad >>> 11) &&& (1 : UInt32)) |||
  (((topQuad >>> 14) &&& (1 : UInt32)) <<< 1) |||
  (((bottomQuad >>> 1) &&& (1 : UInt32)) <<< 2) |||
  (((bottomQuad >>> 4) &&& (1 : UInt32)) <<< 3)

@[inline]
def extractCenterMidUInt (q0 q1 q2 q3 : UInt32) : UInt32 :=
  ((q0 >>> 15) &&& (1 : UInt32)) |||
  (((q1 >>> 10) &&& (1 : UInt32)) <<< 1) |||
  (((q2 >>> 5) &&& (1 : UInt32)) <<< 2) |||
  (((q3 >>> 0) &&& (1 : UInt32)) <<< 3)

@[inline]
def quad0UInt (w : UInt64) : UInt32 := (w &&& (0xFFFF : UInt64)).toUInt32

@[inline]
def quad1UInt (w : UInt64) : UInt32 := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32

@[inline]
def quad2UInt (w : UInt64) : UInt32 := ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32

@[inline]
def quad3UInt (w : UInt64) : UInt32 := ((w >>> 48) &&& (0xFFFF : UInt64)).toUInt32

@[export computeNextGen4x4BitwiseUInt]
def computeNextGen4x4BitwiseUInt (w : UInt32) : UInt32 :=
  let b22 := bitRuleUInt (neighborCount22UInt w) ((w >>> 12) &&& (1 : UInt32))
  let b12 := bitRuleUInt (neighborCount12UInt w) ((w >>> 9) &&& (1 : UInt32))
  let b21 := bitRuleUInt (neighborCount21UInt w) ((w >>> 6) &&& (1 : UInt32))
  let b11 := bitRuleUInt (neighborCount11UInt w) ((w >>> 3) &&& (1 : UInt32))
  (b22 <<< 3) ||| (b12 <<< 2) ||| (b21 <<< 1) ||| b11

@[export computeNextGen4x4UInt, noinline]
def computeNextGen4x4UInt (w : UInt32) : UInt32 :=
  computeNextGen4x4BitwiseUInt w

attribute [kotlin_expr "computeNextGen4x4({0})"] computeNextGen4x4UInt


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

end Algorithm

