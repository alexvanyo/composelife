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
-- Level 3 Leaf Node 4x4 Central Splicing (Quadtree Bit Representation)
-- =========================================================================

/--
Computes the packed 16-bit word from four 4-bit quadrants (nibbles),
matching HashLifeAlgorithm.kt centeredSubnodeLevel3:
  node.nw.se + node.ne.sw * 16 + node.sw.ne * 256 + node.se.nw * 4096
-/
def packCentralNibbles (q0 q1 q2 q3 : ℕ) : ℕ :=
  q0 + q1 * 16 + q2 * 256 + q3 * 4096

/--
Extracts the central 4x4 from an 8x8 packed leaf node (64-bit word).
Matches centeredSubnodeLevel3 in Kotlin.
-/
def centeredSubnodeLevel3Bits (leaf : ℕ) : ℕ :=
  let nw := (leaf / (2^0)) % (2^16)
  let ne := (leaf / (2^16)) % (2^16)
  let sw := (leaf / (2^32)) % (2^16)
  let se := (leaf / (2^48)) % (2^16)
  let q0 := (nw / (2^12)) % 16
  let q1 := (ne / (2^8)) % 16
  let q2 := (sw / (2^4)) % 16
  let q3 := (se / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Extracts the horizontal central 4x4 spanning west and east 8x8 leaf nodes.
Matches centeredHorizontalSubnodeLevel3 in Kotlin.
-/
def centeredHorizontalSubnodeLevel3Bits (w e : ℕ) : ℕ :=
  let w_ne := (w / (2^16)) % (2^16)
  let w_se := (w / (2^48)) % (2^16)
  let e_nw := (e / (2^0)) % (2^16)
  let e_sw := (e / (2^32)) % (2^16)
  let q0 := (w_ne / (2^12)) % 16
  let q1 := (e_nw / (2^8)) % 16
  let q2 := (w_se / (2^4)) % 16
  let q3 := (e_sw / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Extracts the vertical central 4x4 spanning north and south 8x8 leaf nodes.
Matches centeredVerticalSubnodeLevel3 in Kotlin.
-/
def centeredVerticalSubnodeLevel3Bits (n s : ℕ) : ℕ :=
  let n_sw := (n / (2^32)) % (2^16)
  let n_se := (n / (2^48)) % (2^16)
  let s_nw := (s / (2^0)) % (2^16)
  let s_ne := (s / (2^16)) % (2^16)
  let q0 := (n_sw / (2^12)) % 16
  let q1 := (n_se / (2^8)) % 16
  let q2 := (s_nw / (2^4)) % 16
  let q3 := (s_ne / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Extracts the center 4x4 from a 16x16 Level 4 node (four 8x8 leaf nodes).
Matches centeredSubSubnodeLevel4 in Kotlin.
-/
def centeredSubSubnodeLevel4Bits (nw ne sw se : ℕ) : ℕ :=
  let nw_se := (nw / (2^48)) % (2^16)
  let ne_sw := (ne / (2^32)) % (2^16)
  let sw_ne := (sw / (2^16)) % (2^16)
  let se_nw := (se / (2^0)) % (2^16)
  let q0 := (nw_se / (2^12)) % 16
  let q1 := (ne_sw / (2^8)) % 16
  let q2 := (sw_ne / (2^4)) % 16
  let q3 := (se_nw / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Packs four 16-bit 4x4 quadrants into a 64-bit 8x8 leaf node.
-/
def packLeafFrom4x4s (q0 q1 q2 q3 : ℕ) : ℕ :=
  (q0 % (2^16)) + (q1 % (2^16)) * (2^16) + (q2 % (2^16)) * (2^32) + (q3 % (2^16)) * (2^48)

/--
Direct computation of next generation for a 16x16 Level 4 MacroCell (four 8x8 leaf nodes)
into its central 8x8 leaf node.
Matches Level4Node.computeNextGeneration in HashLifeAlgorithm.kt.
-/
def computeLevel4NextGen16x16 (nw ne sw se : ℕ) : ℕ :=
  let n00 := centeredSubnodeLevel3Bits nw
  let n01 := centeredHorizontalSubnodeLevel3Bits nw ne
  let n02 := centeredSubnodeLevel3Bits ne
  let n10 := centeredVerticalSubnodeLevel3Bits nw sw
  let n11 := centeredSubSubnodeLevel4Bits nw ne sw se
  let n12 := centeredVerticalSubnodeLevel3Bits ne se
  let n20 := centeredSubnodeLevel3Bits sw
  let n21 := centeredHorizontalSubnodeLevel3Bits sw se
  let n22 := centeredSubnodeLevel3Bits se

  let leafNW := packLeafFrom4x4s n00 n01 n10 n11
  let leafNE := packLeafFrom4x4s n01 n02 n11 n12
  let leafSW := packLeafFrom4x4s n10 n11 n20 n21
  let leafSE := packLeafFrom4x4s n11 n12 n21 n22

  let outNW := computeLeafNextGen8x8Branch leafNW
  let outNE := computeLeafNextGen8x8Branch leafNE
  let outSW := computeLeafNextGen8x8Branch leafSW
  let outSE := computeLeafNextGen8x8Branch leafSE

  packLeafFrom4x4s outNW outNE outSW outSE

-- =========================================================================
-- Fixed-width UInt32 / UInt64 HashLife Computations are defined in Algorithm.MacroCell
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

def hexChar (n : UInt8) : Char :=
  if n < 10 then (Char.ofNat (48 + n.toNat))
  else (Char.ofNat (97 + (n.toNat - 10)))

def generateLUTHex : String × String := Id.run do
  let mut s0 := ""
  let mut s1 := ""
  for i in [:32768] do
    let r0 := computeNextGen4x4BitwiseUInt i.toUInt32
    s0 := s0.push (hexChar r0.toUInt8)
    let r1 := computeNextGen4x4BitwiseUInt (i + 32768).toUInt32
    s1 := s1.push (hexChar r1.toUInt8)
  (s0, s1)

def generateLUTKotlin : String := Id.run do
  let (h0, h1) := generateLUTHex
  s!"private const val LUT_HEX_0 = \"{h0}\"\n\n" ++
  s!"private const val LUT_HEX_1 = \"{h1}\"\n\n" ++
  "/**\n" ++
  " * A 64 KB lookup table mapping any 16-bit 4x4 grid in Morton order to its next generation 2x2 center (4 bits).\n" ++
  " *\n" ++
  " * Precomputed from the formally verified Lean Conway transition rule for all 65,536 neighborhood states.\n" ++
  " */\n" ++
  "@PublishedApi\n" ++
  "internal val NEXT_GEN_4X4_LUT: ByteArray = run {\n" ++
  "    val arr = ByteArray(65536)\n" ++
  "    for (i in 0 until 32768) {\n" ++
  "        val c0 = LUT_HEX_0[i]\n" ++
  "        arr[i] = if (c0 <= '9') (c0.code - 48).toByte() else (c0.code - 87).toByte()\n" ++
  "        val c1 = LUT_HEX_1[i]\n" ++
  "        arr[32768 + i] = if (c1 <= '9') (c1.code - 48).toByte() else (c1.code - 87).toByte()\n" ++
  "    }\n" ++
  "    arr\n" ++
  "}"

@[kotlin_file]
def hashLifeFileSpec : FileSpec := {
  imports := #[
    "import com.alexvanyo.composelife.model.MacroCell"
  ]
  items := #[
    .verbatim generateLUTKotlin,
    .topLevel
  ]
}

end Algorithm
