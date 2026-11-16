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

/-!
# Standalone Lean Model of Hand-Written `BitComputation.kt`

Pure Lean mathematical model of the hand-written production Kotlin functions in
`algorithm/src/commonMain/kotlin/com/alexvanyo/composelife/algorithm/BitComputation.kt`.

This file intentionally does **not** import `Lean.Compiler.Kotlin` and is never exported to Kotlin:
the Kotlin code is hand-written and serves as the target verified against this model via
JVM bytecode lifting (`Algorithm.KotlinJvmBytecode`).
-/

namespace Algorithm.KotlinModel

/-- Pure Lean model of `computeQuadInfo(q: Int): Int` from `BitComputation.kt`. -/
def computeQuadInfoModel (q : UInt32) : UInt32 :=
  let c : UInt32 := q >>> 3
  let center : UInt32 :=
    (c &&& (1 : UInt32)) ||| ((c >>> 2) &&& (2 : UInt32)) |||
      ((c >>> 4) &&& (4 : UInt32)) ||| ((c >>> 6) &&& (8 : UInt32))
  let right : UInt32 :=
    ((q >>> 7) &&& (1 : UInt32)) ||| (((q >>> 13) &&& (1 : UInt32)) <<< 2)
  let left : UInt32 :=
    (((q >>> 2) &&& (1 : UInt32)) <<< 1) ||| (((q >>> 8) &&& (1 : UInt32)) <<< 3)
  let bottom : UInt32 :=
    ((q >>> 11) &&& (1 : UInt32)) ||| (((q >>> 14) &&& (1 : UInt32)) <<< 1)
  let top : UInt32 :=
    (((q >>> 1) &&& (1 : UInt32)) <<< 2) ||| (((q >>> 4) &&& (1 : UInt32)) <<< 3)
  let corner : UInt32 :=
    ((q >>> 15) &&& (1 : UInt32)) ||| (((q >>> 10) &&& (1 : UInt32)) <<< 1) |||
      (((q >>> 5) &&& (1 : UInt32)) <<< 2) ||| ((q &&& (1 : UInt32)) <<< 3)
  center ||| (right <<< 4) ||| (left <<< 8) ||| (bottom <<< 12) ||| (top <<< 16) ||| (corner <<< 20)

/-- Entry `k` of `QUAD_INFO_LUT = IntArray(65536, ::computeQuadInfo)`. -/
def quadInfoEntry (k : Nat) : UInt32 :=
  computeQuadInfoModel (UInt32.ofNat k)

/--
Pure Lean model of `Long.computeNextGenerationPureKotlin(): Int` from `BitComputation.kt`,
parameterized over a 4×4 next-generation lookup oracle (matching `NEXT_GEN_4X4_LUT[...]`).
-/
def computeNextGenerationPureKotlinModelWith (nextGenLut : UInt32 → UInt32) (w : UInt64) : UInt32 :=
  if w == 0 then 0
  else
    let q0 : UInt32 := (w &&& (0xFFFF : UInt64)).toUInt32
    let q1 : UInt32 := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
    let q2 : UInt32 := ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
    let q3 : UInt32 := (w >>> 48).toUInt32
    let info0 : UInt32 := computeQuadInfoModel q0
    let info1 : UInt32 := computeQuadInfoModel q1
    let info2 : UInt32 := computeQuadInfoModel q2
    let info3 : UInt32 := computeQuadInfoModel q3
    let n00 : UInt32 := info0 &&& (0xF : UInt32)
    let n02 : UInt32 := info1 &&& (0xF : UInt32)
    let n20 : UInt32 := info2 &&& (0xF : UInt32)
    let n22 : UInt32 := info3 &&& (0xF : UInt32)
    let n01 : UInt32 := ((info0 >>> 4) &&& (0x5 : UInt32)) ||| ((info1 >>> 8) &&& (0xA : UInt32))
    let n21 : UInt32 := ((info2 >>> 4) &&& (0x5 : UInt32)) ||| ((info3 >>> 8) &&& (0xA : UInt32))
    let n10 : UInt32 := ((info0 >>> 12) &&& (0x3 : UInt32)) ||| ((info2 >>> 16) &&& (0xC : UInt32))
    let n12 : UInt32 := ((info1 >>> 12) &&& (0x3 : UInt32)) ||| ((info3 >>> 16) &&& (0xC : UInt32))
    let n11 : UInt32 :=
      ((info0 >>> 20) &&& (1 : UInt32)) |||
      ((info1 >>> 20) &&& (2 : UInt32)) |||
      ((info2 >>> 20) &&& (4 : UInt32)) |||
      ((info3 >>> 20) &&& (8 : UInt32))
    let nw : UInt32 := nextGenLut (n00 ||| (n01 <<< 4) ||| (n10 <<< 8) ||| (n11 <<< 12))
    let ne : UInt32 := nextGenLut (n01 ||| (n02 <<< 4) ||| (n11 <<< 8) ||| (n12 <<< 12))
    let sw : UInt32 := nextGenLut (n10 ||| (n11 <<< 4) ||| (n20 <<< 8) ||| (n21 <<< 12))
    let se : UInt32 := nextGenLut (n11 ||| (n12 <<< 4) ||| (n21 <<< 8) ||| (n22 <<< 12))
    nw ||| (ne <<< 4) ||| (sw <<< 8) ||| (se <<< 12)

/-- Pure Lean model of `Long.computeNextGenerationPureKotlin()` with `Algorithm.computeNextGen4x4BitwiseUInt`. -/
def computeNextGenerationPureKotlinModel (w : UInt64) : UInt32 :=
  computeNextGenerationPureKotlinModelWith Algorithm.computeNextGen4x4BitwiseUInt w

end Algorithm.KotlinModel
