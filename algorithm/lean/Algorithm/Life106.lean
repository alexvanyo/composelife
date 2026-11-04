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

import Lean.Compiler.Kotlin
import Init.Data.UInt

namespace Algorithm

@[kotlin_class "Life106Result"]
structure Life106Result where
  status : UInt32
  errLineIndex : UInt32
  errLineContent : String
  cells : Array (Int32 × Int32)
  deriving DecidableEq, Repr

@[inline]
def isDigit (b : UInt8) : Bool := b >= 48 && b <= 57

@[inline]
def isSpace (b : UInt8) : Bool := b == 32 || b == 9 || b == 13

structure ParseIntResult where
  val : Int32
  nextPos : UInt32
  deriving DecidableEq, Repr

def parseSignedIntAt (bytes : ByteArray) (pos limit : UInt32) : Option ParseIntResult :=
  if pos >= limit then none
  else
    let isNeg := bytes.get! pos.toNat == 45
    let startDigits := if isNeg then pos + 1 else pos
    if startDigits >= limit then none
    else
      let rec loop (p : UInt32) (acc : UInt32) (hasDigits : Bool) : Option ParseIntResult :=
        if h : p < limit then
          have : limit.toNat - (p + 1).toNat < limit.toNat - p.toNat := by
            have h1 := UInt32.lt_iff_toNat_lt.mp h
            have h2 : (p + 1).toNat = p.toNat + 1 := by
              rw [UInt32.toNat_add]
              have := UInt32.toNat_lt limit
              simp only [UInt32.toNat_one]
              omega
            omega
          let b := bytes.get! p.toNat
          if isDigit b then
            loop (p + 1) (acc * 10 + (b.toUInt32 - 48)) true
          else if hasDigits then
            let v := if isNeg then (0 : Int32) - acc.toInt32 else acc.toInt32
            some ⟨v, p⟩
          else
            none
        else if hasDigits then
          let v := if isNeg then (0 : Int32) - acc.toInt32 else acc.toInt32
          some ⟨v, p⟩
        else
          none
      termination_by limit.toNat - p.toNat
      loop startDigits 0 false

def skipSpaces (bytes : ByteArray) (pos limit : UInt32) : UInt32 :=
  if h : pos < limit then
    have : limit.toNat - (pos + 1).toNat < limit.toNat - pos.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (pos + 1).toNat = pos.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    if isSpace (bytes.get! pos.toNat) then
      skipSpaces bytes (pos + 1) limit
    else
      pos
  else
    pos
termination_by limit.toNat - pos.toNat

def parseCoordLine (line : String) : Option (Int32 × Int32) :=
  let bytes := line.toByteArray
  let limit := bytes.size.toUInt32
  let p0 := skipSpaces bytes 0 limit
  match parseSignedIntAt bytes p0 limit with
  | none => none
  | some res1 =>
    if res1.nextPos >= limit || !isSpace (bytes.get! res1.nextPos.toNat) then none
    else
      let p1 := skipSpaces bytes res1.nextPos limit
      match parseSignedIntAt bytes p1 limit with
      | none => none
      | some res2 =>
        let p2 := skipSpaces bytes res2.nextPos limit
        if p2 == limit then
          some (res1.val, res2.val)
        else
          none

@[export life106_deserialize]
def deserializeLife106 (lines : Array String) : Life106Result :=
  if lines.size.toUInt32 == 0 then
    ⟨1, 0, "", #[]⟩
  else
    let header := lines[0]!
    if header != "#Life 1.06" then
      ⟨2, 1, header, #[]⟩
    else
      let rec loop (i : UInt32) (limit : UInt32) (acc : Array (Int32 × Int32)) : Life106Result :=
        if h : i < limit then
          have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
            have h1 := UInt32.lt_iff_toNat_lt.mp h
            have h2 : (i + 1).toNat = i.toNat + 1 := by
              rw [UInt32.toNat_add]
              have := UInt32.toNat_lt limit
              simp only [UInt32.toNat_one]
              omega
            omega
          let line := lines[i.toNat]!
          match parseCoordLine line with
          | some coord => loop (i + 1) limit (acc.push coord)
          | none => ⟨3, i + 1, line, #[]⟩
        else
          ⟨0, 0, "", acc⟩
      termination_by limit.toNat - i.toNat
      loop 1 lines.size.toUInt32 #[]

@[export life106_serialize]
def serializeLife106 (cells : Array (Int32 × Int32)) : Array String :=
  let rec loop (i : UInt32) (limit : UInt32) (acc : Array String) : Array String :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let (x, y) := cells[i.toNat]!
      loop (i + 1) limit (acc.push s!"{x} {y}")
    else
      acc
  termination_by limit.toNat - i.toNat
  loop 0 cells.size.toUInt32 #["#Life 1.06"]

end Algorithm
