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
import Lean.Compiler.Kotlin

open Lean.Compiler.Kotlin

local notation "ℕ" => Nat

namespace Algorithm

-- =========================================================================
-- Kotlin Exports of the Fixed-width HashLife Computations (defined in Algorithm.MacroCell)
-- =========================================================================

@[export computeNextGen4x4BitwiseUInt]
def exportComputeNextGen4x4BitwiseUInt (w : UInt32) : UInt32 :=
  computeNextGen4x4BitwiseUInt w

@[export computeNextGen4x4UInt]
def exportComputeNextGen4x4UInt (w : UInt32) : UInt32 :=
  computeNextGen4x4UInt w

@[export computeLeafNextGen8x8BranchUInt]
def exportComputeLeafNextGen8x8BranchUInt (w : UInt64) : UInt32 :=
  computeLeafNextGen8x8BranchUInt w

/--
The 64 KB lookup table behind Kotlin's `computeNextGen4x4`, mapping every 16-bit 4x4 grid in Morton order to its
next generation 2x2 center (4 bits). It is filled when first used by running the compiled
`computeNextGen4x4BitwiseUInt` on every index, so each entry is exactly that function's result.
-/
def nextGen4x4LutKotlin : String :=
  "/**\n" ++
  " * A 64 KB lookup table mapping any 16-bit 4x4 grid in Morton order to its next generation 2x2 center (4 bits).\n" ++
  " *\n" ++
  " * Entry `i` is `computeNextGen4x4BitwiseUInt(i)`, the formally verified Lean Conway transition.\n" ++
  " */\n" ++
  "@PublishedApi\n" ++
  "internal val NEXT_GEN_4X4_LUT: ByteArray = ByteArray(65536) {\n" ++
  "    f_Algorithm_computeNextGen4x4BitwiseUInt(it.toUInt()).toByte()\n" ++
  "}"

@[kotlin_file]
def hashLifeFileSpec : FileSpec := {
  imports := #[
    "import com.alexvanyo.composelife.model.MacroCell"
  ]
  items := #[
    .verbatim nextGen4x4LutKotlin,
    .topLevel
  ]
}

end Algorithm
