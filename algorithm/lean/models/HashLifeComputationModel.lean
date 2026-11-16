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
import AlgorithmDefs
import models.BitComputationModel

namespace Algorithm.KotlinModel

/-!
# Standalone Mathematical Model of Hand-Written `HashLifeComputation.kt`

Pure Lean 4 specification modeling `packLeafNode`, `LeafNode.{nw,ne,sw,se}`,
the centered subnode extractors (`centeredSubnodeLevel3`,
`centeredHorizontalSubnodeLevel3`, `centeredVerticalSubnodeLevel3`,
`centeredSubSubnodeLevel4`), and `computeLevel4NextGeneration` without relying
on Lean-to-Kotlin codegen as source of truth.
-/

def packLeafNodeModel (nw ne sw se : UInt32) : UInt64 :=
  (nw.toUInt64 &&& (0xffff : UInt64)) |||
  ((ne.toUInt64 &&& (0xffff : UInt64)) <<< 16) |||
  ((sw.toUInt64 &&& (0xffff : UInt64)) <<< 32) |||
  ((se.toUInt64 &&& (0xffff : UInt64)) <<< 48)

def leafNwModel (w : UInt64) : UInt32 := (w &&& (0xffff : UInt64)).toUInt32
def leafNeModel (w : UInt64) : UInt32 := ((w >>> 16) &&& (0xffff : UInt64)).toUInt32
def leafSwModel (w : UInt64) : UInt32 := ((w >>> 32) &&& (0xffff : UInt64)).toUInt32
def leafSeModel (w : UInt64) : UInt32 := (w >>> 48).toUInt32

def centeredSubnodeLevel3Model (w : UInt64) : UInt32 :=
  let nw := leafNwModel w
  let ne := leafNeModel w
  let sw := leafSwModel w
  let se := leafSeModel w
  ((nw >>> 12) &&& (15 : UInt32)) |||
  (((ne >>> 8) &&& (15 : UInt32)) <<< 4) |||
  (((sw >>> 4) &&& (15 : UInt32)) <<< 8) |||
  ((se &&& (15 : UInt32)) <<< 12)

def centeredHorizontalSubnodeLevel3Model (nw ne : UInt64) : UInt32 :=
  let l0 := leafNeModel nw
  let l1 := leafSeModel nw
  let r0 := leafNwModel ne
  let r1 := leafSwModel ne
  ((l0 >>> 12) &&& (15 : UInt32)) |||
  (((r0 >>> 8) &&& (15 : UInt32)) <<< 4) |||
  (((l1 >>> 4) &&& (15 : UInt32)) <<< 8) |||
  ((r1 &&& (15 : UInt32)) <<< 12)

def centeredVerticalSubnodeLevel3Model (nw sw : UInt64) : UInt32 :=
  let t0 := leafSwModel nw
  let t1 := leafSeModel nw
  let b0 := leafNwModel sw
  let b1 := leafNeModel sw
  ((t0 >>> 12) &&& (15 : UInt32)) |||
  (((t1 >>> 8) &&& (15 : UInt32)) <<< 4) |||
  (((b0 >>> 4) &&& (15 : UInt32)) <<< 8) |||
  ((b1 &&& (15 : UInt32)) <<< 12)

def centeredSubSubnodeLevel4Model (nw ne sw se : UInt64) : UInt32 :=
  let a := leafSeModel nw
  let b := leafSwModel ne
  let c := leafNeModel sw
  let d := leafNwModel se
  ((a >>> 12) &&& (15 : UInt32)) |||
  (((b >>> 8) &&& (15 : UInt32)) <<< 4) |||
  (((c >>> 4) &&& (15 : UInt32)) <<< 8) |||
  ((d &&& (15 : UInt32)) <<< 12)

def computeLevel4NextGenerationModel
    (nw ne sw se : UInt64)
    (computeLeafNextGen : UInt64 → UInt32 := computeNextGenerationPureKotlinModel) : UInt64 :=
  let n00 := centeredSubnodeLevel3Model nw
  let n10 := centeredHorizontalSubnodeLevel3Model nw ne
  let n20 := centeredSubnodeLevel3Model ne
  let n01 := centeredVerticalSubnodeLevel3Model nw sw
  let n11 := centeredSubSubnodeLevel4Model nw ne sw se
  let n21 := centeredVerticalSubnodeLevel3Model ne se
  let n02 := centeredSubnodeLevel3Model sw
  let n12 := centeredHorizontalSubnodeLevel3Model sw se
  let n22 := centeredSubnodeLevel3Model se
  let outNw := computeLeafNextGen (packLeafNodeModel n00 n10 n01 n11)
  let outNe := computeLeafNextGen (packLeafNodeModel n10 n20 n11 n21)
  let outSw := computeLeafNextGen (packLeafNodeModel n01 n11 n02 n12)
  let outSe := computeLeafNextGen (packLeafNodeModel n11 n21 n12 n22)
  packLeafNodeModel outNw outNe outSw outSe

/-- Bit-level state of a 16×16 Level-4 Conway cell grid composed of four 8×8 leaves `(nw, ne, sw, se)`. -/
def level4CellAt (nw ne sw se : UInt64) (x y : Int) : Bool :=
  if x < 0 ∨ x ≥ 16 ∨ y < 0 ∨ y ≥ 16 then false
  else
    let q := if x < 8 then (if y < 8 then nw else sw) else (if y < 8 then ne else se)
    let lx := if x < 8 then x else x - 8
    let ly := if y < 8 then y else y - 8
    Algorithm.leafAt q lx ly

end Algorithm.KotlinModel
