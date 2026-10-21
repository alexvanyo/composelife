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

import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.HashLife
import AlgorithmDefs
import proofs.HashLifeKernelProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Bit-level stepping kernels

Each compiled kernel computes one Conway generation of the cells it covers, for every input word. The cell
functions are `grid4At` (a 4x4 grid in Morton order), `leafAt` (an 8x8 leaf) and `quadSel` of four leaves (a
16x16 Level 4 node), and the rule is `nextGenAt`.
-/

/-- The 4x4 kernel: each of its four output bits is one generation of the corresponding center cell. -/
theorem computeNextGen4x4UInt_correct (w : UInt32) (x y : ℤ) (hx : 1 ≤ x ∧ x ≤ 2) (hy : 1 ≤ y ∧ y ≤ 2) :
    (computeNextGen4x4UInt w).toBitVec.getLsbD (mortonIndex4 (x - 1).toNat (y - 1).toNat) =
      nextGenAt (grid4At w) x y :=
  computeNextGen4x4UInt_spec w x y hx hy

/-- The 4x4 kernel's result fits in 4 bits. -/
theorem computeNextGen4x4UInt_lt_16 (w : UInt32) : (computeNextGen4x4UInt w).toNat < 16 :=
  computeNextGen4x4UInt_lt w

/--
The generated Kotlin replaces `computeNextGen4x4UInt w` by `computeNextGen4x4(w)`, which reads entry
`w and 0xFFFF` of `NEXT_GEN_4X4_LUT` (filled with `computeNextGen4x4BitwiseUInt`) and keeps 4 bits. This is the
same function.
-/
theorem computeNextGen4x4UInt_eq_lookup (w : UInt32) :
    computeNextGen4x4UInt w = computeNextGen4x4BitwiseUInt (w &&& 0xFFFF) &&& 0xF :=
  computeNextGen4x4UInt_eq_table w

/-- The 8x8 leaf kernel: each of its 16 output bits is one generation of the corresponding center cell. -/
theorem computeLeafNextGen8x8BranchUInt_correct (w : UInt64) (x y : ℤ) (hx : 2 ≤ x ∧ x < 6) (hy : 2 ≤ y ∧ y < 6) :
    (computeLeafNextGen8x8BranchUInt w).toBitVec.getLsbD (mortonIndex4 (x - 2).toNat (y - 2).toNat) =
      nextGenAt (leafAt w) x y :=
  computeLeafNextGen8x8BranchUInt_spec w x y hx hy

/-- The 16x16 Level 4 kernel: its output leaf is one generation of the central 8x8 cells. -/
theorem computeLevel4NextGen16x16UInt_correct (a b c d : UInt64) (x y : ℤ)
    (hx0 : 0 ≤ x) (hx : x < 8) (hy0 : 0 ≤ y) (hy : y < 8) :
    leafAt (computeLevel4NextGen16x16UInt a b c d) x y =
      nextGenAt (quadSel (leafAt a) (leafAt b) (leafAt c) (leafAt d) 8) (x + 4) (y + 4) :=
  leafAt_computeLevel4NextGen16x16UInt a b c d x y hx0 hx hy0 hy

/-- The empty-leaf shortcut of `computeLeafNextGen8x8BranchUInt` does not change its result. -/
theorem computeLeafNextGen8x8BranchUInt_eq_fastUInt (w : UInt64) :
    computeLeafNextGen8x8BranchUInt w = computeLeafNextGen8x8FastUInt w :=
  computeLeafNextGen8x8BranchUInt_eq_fast w

end Algorithm
