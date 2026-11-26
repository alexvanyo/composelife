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

namespace Algorithm.KotlinModel

/-- Pack signed 32-bit `(x, y)` into Compose `IntOffset` (`Long`). -/
def packCellOffset (x y : Int32) : UInt64 :=
  (x.toUInt32.toUInt64 <<< 32) ||| y.toUInt32.toUInt64

def cellOffsetX (p : UInt64) : Int32 :=
  (p >>> 32).toUInt32.toInt32

def cellOffsetY (p : UInt64) : Int32 :=
  p.toUInt32.toInt32

def addCellOffset (a b : UInt64) : UInt64 :=
  packCellOffset (cellOffsetX a + cellOffsetX b) (cellOffsetY a + cellOffsetY b)

def subCellOffset (a b : UInt64) : UInt64 :=
  packCellOffset (cellOffsetX a - cellOffsetX b) (cellOffsetY a - cellOffsetY b)

/-- Deduplicate a list of packed `IntOffset`s preserving first occurrence. -/
def dedupOffsets : List UInt64 → List UInt64
  | [] => []
  | x :: xs => if xs.contains x then dedupOffsets xs else x :: dedupOffsets xs

/-- Standalone model of `CellState.withCell(offset, isAlive)`. -/
def withCellModel (cells : List UInt64) (p : UInt64) (isAlive : Bool) : List UInt64 :=
  if isAlive then
    if cells.contains p then cells else cells ++ [p]
  else
    cells.filter (· != p)

/-- Standalone model of `CellState.offsetBy(offset)`. -/
def offsetByModel (cells : List UInt64) (delta : UInt64) : List UInt64 :=
  cells.map (fun c => addCellOffset c delta)

/-- Standalone model of `CellState.equals(other)`. -/
def cellStateEqualsModel (a b : List UInt64) : Bool :=
  a.length == b.length && b.all (fun x => a.contains x)

/-- Bounding box `(left, top, right, bottom)` for a list of packed `IntOffset`s (`(0, 0, 0, 0)` if empty). -/
def boundingBoxModel (cells : List UInt64) : Int32 × Int32 × Int32 × Int32 :=
  match cells with
  | [] => (0, 0, 0, 0)
  | c :: cs =>
    let minX := cs.foldl (fun m p => if (cellOffsetX p) < m then cellOffsetX p else m) (cellOffsetX c)
    let minY := cs.foldl (fun m p => if (cellOffsetY p) < m then cellOffsetY p else m) (cellOffsetY c)
    let maxX := cs.foldl (fun m p => if m < (cellOffsetX p) then cellOffsetX p else m) (cellOffsetX c)
    let maxY := cs.foldl (fun m p => if m < (cellOffsetY p) then cellOffsetY p else m) (cellOffsetY c)
    (minX, minY, maxX + 1, maxY + 1)

end Algorithm.KotlinModel
