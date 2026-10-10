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
import Algorithm.HashLife
import AlgorithmDefs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Semantic Cell Model of MacroCells
-- =========================================================================

/--
Morton (Z-order) bit index of the cell at relative coordinates (x, y) within an 8x8 leaf,
matching `cellToLeafBitUInt` and the inverse of `bitToCoord8x8`.
-/
def mortonIndex (x y : ℕ) : ℕ :=
  x % 2 + 2 * (y % 2) + 4 * (x / 2 % 2) + 8 * (y / 2 % 2) + 16 * (x / 4) + 32 * (y / 4)

/--
Whether the 8x8 leaf has an alive cell at relative coordinates (x, y).
Coordinates outside of [0, 8) x [0, 8) are dead.
-/
def leafAt (leaf : UInt64) (x y : ℤ) : Bool :=
  if 0 ≤ x ∧ x < 8 ∧ 0 ≤ y ∧ y < 8 then
    leaf.toBitVec.getLsbD (mortonIndex x.toNat y.toNat)
  else false

/--
Combines four quadrant cell functions of width `w` into a cell function of width `2 * w`.
Coordinates outside of [0, 2w) x [0, 2w) are dead.
-/
def quadSel (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ) : Bool :=
  if 0 ≤ x ∧ x < 2 * w ∧ 0 ≤ y ∧ y < 2 * w then
    if x < w then
      if y < w then f1 x y else f3 x (y - w)
    else
      if y < w then f2 (x - w) y else f4 (x - w) (y - w)
  else false

/--
Whether the MacroCell has an alive cell at relative coordinates (x, y).
-/
def cellAt : MacroCell → ℤ → ℤ → Bool
  | .level4Node _ nw ne sw se, x, y =>
    quadSel (leafAt nw) (leafAt ne) (leafAt sw) (leafAt se) 8 x y
  | .cellNode _ nw ne sw se, x, y =>
    quadSel (cellAt nw) (cellAt ne) (cellAt sw) (cellAt se) ((2 : ℤ) ^ nw.level.toNat) x y

/--
Number of alive Moore neighbors of (x, y) for an arbitrary cell function.
-/
def neighborCountAt (f : ℤ → ℤ → Bool) (x y : ℤ) : ℕ :=
  (mooreOffsets.filter (fun d => f (x + d.1) (y + d.2))).length

/--
Conway's rule applied pointwise to an arbitrary cell function.
-/
def nextGenAt (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  lifeRule (f x y) (neighborCountAt f x y)

/--
Structural well-formedness at an explicit tree depth: every Level4Node is at depth 4,
and every CellNode at depth `d` has four children at depth `d - 1`.
-/
def WFd : MacroCell → ℕ → Prop
  | .level4Node .., d => d = 4
  | .cellNode _ nw ne sw se, d =>
    5 ≤ d ∧ WFd nw (d - 1) ∧ WFd ne (d - 1) ∧ WFd sw (d - 1) ∧ WFd se (d - 1)



-- =========================================================================
-- Int32 Representability Predicates
-- =========================================================================

def minInt32 : ℤ := -2147483648
def maxInt32 : ℤ := 2147483647

/--
Predicate asserting that a HashLifeCellState is representable within standard
32-bit integer limits:
- Tree level bound: 4 <= level <= 30 (preventing bitshift overflow in 2^level).
- Universe bounds and offsets strictly remain within [-2^31, 2^31 - 1].
- Tree depth bound: depth <= 30, so the UInt32 `level` of every subtree is its exact depth.
  This also bounds the population by 4^30 = 2^60, so the UInt64 `size` comparison in
  `needToExpand` cannot be fooled by wraparound.
-/
def isInInt32Bounds (st : HashLifeCellState) : Prop :=
  st.macroCell.level.toNat >= 4 ∧
  st.macroCell.level.toNat <= 30 ∧
  st.offset.1 >= minInt32 ∧ st.offset.1 <= maxInt32 ∧
  st.offset.2 >= minInt32 ∧ st.offset.2 <= maxInt32 ∧
  st.offset.1 + (2 : ℤ) ^ st.macroCell.level.toNat <= maxInt32 ∧
  st.offset.2 + (2 : ℤ) ^ st.macroCell.level.toNat <= maxInt32 ∧
  st.macroCell.depth <= 30

/--
Predicate asserting that a state remains within Int32 representability limits
across all n successive generations.
-/
def isInInt32BoundsN (n : ℕ) (st : HashLifeCellState) : Prop :=
  ∀ (k : ℕ), k <= n → isInInt32Bounds (hashLifeStepN k st)

-- =========================================================================
-- Structural and Level Invariants
-- =========================================================================

theorem hashLifeStepRecursiveAux_fuel_level4 (fuel : ℕ) (nw ne sw se : UInt64) :
    hashLifeStepRecursiveAux (fuel + 1) (.level4Node 0 nw ne sw se) =
    makeLevel4Node 0 0 0 (computeLevel4NextGen16x16UInt nw ne sw se) := by
  dsimp [hashLifeStepRecursiveAux, MacroCell.level]

theorem hashLifeStepRecursive_level4 (nw ne sw se : UInt64) :
    hashLifeStepRecursive (.level4Node 0 nw ne sw se) =
    makeLevel4Node 0 0 0 (computeLevel4NextGen16x16UInt nw ne sw se) := by
  dsimp [hashLifeStepRecursive]
  change hashLifeStepRecursiveAux 4 (.level4Node 0 nw ne sw se) = _
  rfl

end Algorithm
