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

import JvmBytecode
import JvmSemantics
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep
import proofs.JvmEquiv.StepExt
import proofs.JvmEquiv.Family5a
import proofs.JvmEquiv.Family5c

namespace Algorithm.JvmVerification

open Algorithm.JvmBytecode

private theorem deserLoop_combine_step {locs locs1 : Nat → JvmVal}
    {jh jh1 : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {lines : Array String}
    {numLines : UInt32} {spec : Algorithm.MacrocellResult} {k1 : Nat}
    (htest : ∀ g,
      runJvmResFast (g + 4) f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩)
    (hstep : ∀ g,
      runJvmResFast (g + k1) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs1, jh1, hp⟩)
    (hrec :
      (spec.status ≠ .ok ∧
        ∃ f2 pc' enc locs' jh',
          decodeMacrocellResult ⟨pc', [enc], locs', jh', hp⟩ enc = some spec ∧
          ∀ g, runJvmResFast (g + f2) f_Algorithm_deserializeMacrocell_loop_prog 6
              (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs1, jh1, hp⟩ =
            some (enc, ⟨pc', [enc], locs', jh', hp⟩)) ∨
      (∃ f2 i'' inLeaf'' bytesAddr'' limit'' p'' col'' x'' y'' leaf''
          nodes'' leaves'' isLeaf'' warns'' locs'' jh'',
        ¬ i'' < numLines ∧
        DeserLoopLocs locs'' lines numLines i'' inLeaf'' bytesAddr'' limit'' p'' col'' x'' y'' leaf''
          nodes'' leaves'' isLeaf'' warns'' ∧
        locs'' 15 = .ext (.mcWarnGrowBuf warns'') ∧
        jh''.statics = [] ∧
        spec = ⟨.ok, warns''.toArray,
          if nodes''.size == 0 then Algorithm.emptyLevel4 else Algorithm.macroCellAt nodes''.data (nodes''.size - 1)⟩ ∧
        ∀ g, runJvmResFast (g + f2) f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs1, jh1, hp⟩ =
          runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs'', jh'', hp⟩)) :
    (spec.status ≠ .ok ∧
      ∃ f pc' enc locs' jh',
        decodeMacrocellResult ⟨pc', [enc], locs', jh', hp⟩ enc = some spec ∧
        ∀ g, runJvmResFast (g + f) f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          some (enc, ⟨pc', [enc], locs', jh', hp⟩)) ∨
    (∃ f i'' inLeaf'' bytesAddr'' limit'' p'' col'' x'' y'' leaf''
        nodes'' leaves'' isLeaf'' warns'' locs'' jh'',
      ¬ i'' < numLines ∧
      DeserLoopLocs locs'' lines numLines i'' inLeaf'' bytesAddr'' limit'' p'' col'' x'' y'' leaf''
        nodes'' leaves'' isLeaf'' warns'' ∧
      locs'' 15 = .ext (.mcWarnGrowBuf warns'') ∧
      jh''.statics = [] ∧
      spec = ⟨.ok, warns''.toArray,
        if nodes''.size == 0 then Algorithm.emptyLevel4 else Algorithm.macroCellAt nodes''.data (nodes''.size - 1)⟩ ∧
      ∀ g, runJvmResFast (g + f) f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs'', jh'', hp⟩) := by
  rcases hrec with ⟨hne, f2, pc', enc, locs', jh', hdec, hrun⟩ |
      ⟨f2, i'', ilf'', bA, lim, p'', cl, x'', y'', lf, nd, lvs, il, wn, locs'', jh'',
        hge, hdl, hw, hst, hsp, hrun⟩
  · refine Or.inl ⟨hne, f2 + k1 + 4, pc', enc, locs', jh', hdec, ?_⟩
    intro g
    rw [show g + (f2 + k1 + 4) = ((g + f2) + k1) + 4 from by omega, htest, hstep, hrun]
  · refine Or.inr ⟨f2 + k1 + 4, i'', ilf'', bA, lim, p'', cl, x'', y'', lf, nd, lvs, il, wn, locs'', jh'',
      hge, hdl, hw, hst, hsp, ?_⟩
    intro g
    rw [show g + (f2 + k1 + 4) = ((g + f2) + k1) + 4 from by omega, htest, hstep, hrun]

private theorem isDigitByte_iff (b : UInt8) :
    Algorithm.isDigitByte b = true ↔ ¬ b < 48 ∧ ¬ (57 : UInt8) < b := by
  revert b; decide

private theorem u32_succ_toNat {a b : UInt32} (h : a < b) : (a + 1).toNat = a.toNat + 1 := by
  have ha := UInt32.lt_iff_toNat_lt.mp h
  have hb := UInt32.toNat_lt b
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt (by simp; omega)

private theorem byteArray_get!_zero {ba : ByteArray} (hlPos : 0 < ba.data.size) :
    ba.get! 0 = ba.data[0] := by
  dsimp only [ByteArray.get!]
  exact getElem!_pos ba.data 0 hlPos

private theorem decodeMacrocellResult_state_irrel {pc1 pc2 : Nat} {stk1 stk2 : List JvmVal}
    {locs1 locs2 : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {v : JvmVal} :
    decodeMacrocellResult ⟨pc1, stk1, locs1, jh, hp⟩ v =
      decodeMacrocellResult ⟨pc2, stk2, locs2, jh, hp⟩ v := rfl

private theorem deserLoop_parseNode_specEq
    {lines : Array String} {numLines i : UInt32} {bytes : ByteArray}
    {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {nl : Algorithm.MCNodeLine}
    (hi : i < numLines) (hiSz : i.toNat < lines.size)
    (hzeroB : (lines[i.toNat].toByteArray.size.toUInt32 == 0) = false)
    (hb35B : (lines[i.toNat].toByteArray.get! 0 == 35) = false)
    (hdig : Algorithm.isDigitByte (lines[i.toNat].toByteArray.get! 0) = true)
    (hsome : Algorithm.parseMCNodeLine lines[i.toNat].toByteArray = some nl) :
    Algorithm.deserializeMacrocell.loop lines numLines i false bytes limit p col x y leaf
        nodes leaves isLeaf warns =
      match parseNodeStepResult lines[i.toNat] i nl nodes leaves isLeaf warns with
      | .inl (nodes', leaves', isLeaf') =>
        Algorithm.deserializeMacrocell.loop lines numLines (i + 1) false lines[i.toNat].toByteArray
          lines[i.toNat].toByteArray.size.toUInt32 0 0 0 0 0 nodes' leaves' isLeaf' warns
      | .inr errRes => errRes := by
  have hlineBang : lines[i.toNat]! = lines[i.toNat] := by simp [hiSz]
  rw [Algorithm.deserializeMacrocell.loop]
  simp only [hi, ↓reduceDIte, hlineBang, hzeroB, Bool.false_eq_true, ↓reduceIte, hb35B, hdig, hsome]
  dsimp only [parseNodeStepResult]
  by_cases hbad : nl.level < 4 || nl.level > Algorithm.maxMacrocellLevel
  · simp only [hbad, ↓reduceIte]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    by_cases h4 : nl.level == 4
    · simp only [h4, ↓reduceIte]
      cases Algorithm.macrocellLeafChild leaves isLeaf nl.nw with
      | none => rfl
      | some c1 =>
      cases Algorithm.macrocellLeafChild leaves isLeaf nl.ne with
      | none => rfl
      | some c2 =>
      cases Algorithm.macrocellLeafChild leaves isLeaf nl.sw with
      | none => rfl
      | some c3 =>
      cases Algorithm.macrocellLeafChild leaves isLeaf nl.se <;> rfl
    · simp only [h4, Bool.false_eq_true, ↓reduceIte]
      cases Algorithm.macrocellCellChild nodes isLeaf nl.level
          (Algorithm.emptyMacroCellUInt32 (nl.level - 1)) nl.nw with
      | none => rfl
      | some c1 =>
      cases Algorithm.macrocellCellChild nodes isLeaf nl.level
          (Algorithm.emptyMacroCellUInt32 (nl.level - 1)) nl.ne with
      | none => rfl
      | some c2 =>
      cases Algorithm.macrocellCellChild nodes isLeaf nl.level
          (Algorithm.emptyMacroCellUInt32 (nl.level - 1)) nl.sw with
      | none => rfl
      | some c3 =>
      cases Algorithm.macrocellCellChild nodes isLeaf nl.level
          (Algorithm.emptyMacroCellUInt32 (nl.level - 1)) nl.se <;> rfl

private theorem deserLoop_finish_err {locs locs1 : Nat → JvmVal} {jh jhBase : Jvm.JvmHeap AlgExt}
    {hp : AlgHeap} {pc' k1 : Nat} {errRes : Algorithm.MacrocellResult}
    (htest : ∀ g,
      runJvmResFast (g + 4) f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩)
    (hstep1 : ∀ f,
      runJvmResFast (f + k1) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        some ((encodeMacrocellResult jhBase errRes).1,
          ⟨pc', [(encodeMacrocellResult jhBase errRes).1], locs1,
            (encodeMacrocellResult jhBase errRes).2, hp⟩))
    (hne : errRes.status ≠ .ok) :
    errRes.status ≠ .ok ∧
      ∃ f pc'' enc locs' jh',
        decodeMacrocellResult ⟨pc'', [enc], locs', jh', hp⟩ enc = some errRes ∧
        ∀ g, runJvmResFast (g + f) f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          some (enc, ⟨pc'', [enc], locs', jh', hp⟩) :=
  ⟨hne, k1 + 4, pc', (encodeMacrocellResult jhBase errRes).1, locs1,
    (encodeMacrocellResult jhBase errRes).2,
    by rw [decodeMacrocellResult_state_irrel (pc2 := 0) (stk2 := []) (locs2 := fun _ => .null)]
       exact decodeMacrocellResult_encode _ hp errRes,
    fun g => by rw [show g + (k1 + 4) = (g + k1) + 4 from by omega, htest, hstep1]⟩

private theorem deserLoop_parseNode_some_inl {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes nodes' : Algorithm.GrowBuf Algorithm.MacroCell}
    {leaves leaves' : Algorithm.GrowBuf UInt64}
    {isLeaf isLeaf' : Algorithm.GrowBuf Bool}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {nl : Algorithm.MCNodeLine} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hwarnBuf : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hstat : jh.statics = [])
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size)
    (h48 : ¬ lines[i.toNat].toByteArray.data[0] < 48)
    (h57 : ¬ (57 : UInt8) < lines[i.toNat].toByteArray.data[0])
    (hsome : Algorithm.parseMCNodeLine lines[i.toNat].toByteArray = some nl)
    (hres : parseNodeStepResult lines[i.toNat] i nl nodes leaves isLeaf warns =
      .inl (nodes', leaves', isLeaf')) :
    ∃ (k : Nat) (locs' : Nat → JvmVal) (jh' : Jvm.JvmHeap AlgExt),
      locs' 15 = .ext (.mcWarnGrowBuf warns) ∧
      DeserLoopLocs locs' lines numLines (i + 1) false jh.objects.size
        lines[i.toNat].toByteArray.size.toUInt32 0 0 0 0 0 nodes' leaves' isLeaf' warns ∧
      jh'.statics = [] ∧
      ∀ f, runJvmResFast (f + k) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh', hp⟩ := by
  have hps := step_deserLoop_parseNode_some (jh := jh) (hp := hp)
    hlocs hwarnBuf hstat hiSz hibv hnz hlPos h48 h57 hsome
  dsimp only at hps
  rw [hres] at hps
  rcases hps with ⟨k, locs', hw15, hdl, hstep⟩
  refine ⟨k, locs', _, hw15, hdl, ?_, hstep⟩
  exact hstat

private theorem deserLoop_parseNode_none_wrap {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hwarnBuf : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hstat : jh.statics = [])
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size)
    (h48 : ¬ lines[i.toNat].toByteArray.data[0] < 48)
    (h57 : ¬ (57 : UInt8) < lines[i.toNat].toByteArray.data[0])
    (hnone : Algorithm.parseMCNodeLine lines[i.toNat].toByteArray = none) :
    ∃ (locs' : Nat → JvmVal) (jhBase : Jvm.JvmHeap AlgExt),
      ∀ f, runJvmResFast (f + 84) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        some ((encodeMacrocellResult jhBase
            ⟨.unexpectedInput lines[i.toNat] i, warns.toArray, Algorithm.emptyLevel4⟩).1,
          ⟨168, [(encodeMacrocellResult jhBase
            ⟨.unexpectedInput lines[i.toNat] i, warns.toArray, Algorithm.emptyLevel4⟩).1],
            locs', (encodeMacrocellResult jhBase
            ⟨.unexpectedInput lines[i.toNat] i, warns.toArray, Algorithm.emptyLevel4⟩).2, hp⟩) := by
  have hstatNone : jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_LEVEL_4" = none := by
    simp [Jvm.JvmHeap.getStatic?, hstat]
  rcases step_deserLoop_parseNode_none (jh := jh) (hp := hp)
      hlocs hwarnBuf hstatNone hiSz hibv hnz hlPos h48 h57 hnone with ⟨locs', hstep⟩
  exact ⟨locs', _, hstep⟩

private theorem deserLoop_parseNode_some_inr {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {nl : Algorithm.MCNodeLine} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {errRes : Algorithm.MacrocellResult}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hwarnBuf : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hstat : jh.statics = [])
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size)
    (h48 : ¬ lines[i.toNat].toByteArray.data[0] < 48)
    (h57 : ¬ (57 : UInt8) < lines[i.toNat].toByteArray.data[0])
    (hsome : Algorithm.parseMCNodeLine lines[i.toNat].toByteArray = some nl)
    (hres : parseNodeStepResult lines[i.toNat] i nl nodes leaves isLeaf warns = .inr errRes) :
    ∃ (k pc' : Nat) (locs' : Nat → JvmVal) (jhBase : Jvm.JvmHeap AlgExt),
      ∀ f, runJvmResFast (f + k) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        some ((encodeMacrocellResult jhBase errRes).1,
          ⟨pc', [(encodeMacrocellResult jhBase errRes).1], locs',
            (encodeMacrocellResult jhBase errRes).2, hp⟩) := by
  have hps := step_deserLoop_parseNode_some (jh := jh) (hp := hp)
    hlocs hwarnBuf hstat hiSz hibv hnz hlPos h48 h57 hsome
  dsimp only at hps
  rw [hres] at hps
  rcases hps with ⟨k, pc', locs', hstep⟩
  exact ⟨k, pc', locs', _, hstep⟩

theorem deserializeMacrocell_loop_step_or_err
    {lines : Array String} {numLines i : UInt32} {inLeaf : Bool}
    {bytesAddr : Nat} {bytes : ByteArray} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i inLeaf bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hwarn15 : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hstat : jh.statics = [])
    (hnumLe : numLines.toNat ≤ lines.size)
    (hlinesLt : lines.size < 2 ^ 31)
    (hbytesLen : ∀ j, j < lines.size → lines[j]!.toByteArray.data.size < 2 ^ 31)
    (hbytes : inLeaf = true →
      jh.get? bytesAddr = some (.byteArray bytes.data) ∧
      limit = bytes.size.toUInt32 ∧
      bytes.data.size < 2 ^ 31 ∧
      p.toNat ≤ limit.toNat) :
    let spec := Algorithm.deserializeMacrocell.loop lines numLines i inLeaf bytes limit p col x y leaf
      nodes leaves isLeaf warns
    (spec.status ≠ .ok ∧
      ∃ f pc' enc locs' jh',
        decodeMacrocellResult ⟨pc', [enc], locs', jh', hp⟩ enc = some spec ∧
        ∀ g, runJvmResFast (g + f) f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          some (enc, ⟨pc', [enc], locs', jh', hp⟩)) ∨
    (∃ f i' inLeaf' bytesAddr' limit' p' col' x' y' leaf' nodes' leaves' isLeaf' warns' locs' jh',
      ¬ i' < numLines ∧
      DeserLoopLocs locs' lines numLines i' inLeaf' bytesAddr' limit' p' col' x' y' leaf'
        nodes' leaves' isLeaf' warns' ∧
      locs' 15 = .ext (.mcWarnGrowBuf warns') ∧
      jh'.statics = [] ∧
      spec = ⟨.ok, warns'.toArray,
        if nodes'.size == 0 then Algorithm.emptyLevel4 else Algorithm.macroCellAt nodes'.data (nodes'.size - 1)⟩ ∧
      ∀ g, runJvmResFast (g + f) f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh', hp⟩) := by
  by_cases hi : i < numLines
  · have hiPlus : (i + 1).toNat = i.toNat + 1 := u32_succ_toNat hi
    have htest : ∀ g,
        runJvmResFast (g + 4) f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 85
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ :=
      fun _ => step_deserLoop_test_true hlocs.h1 hlocs.h2 hi
    have hiSz : i.toNat < lines.size := Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hi) hnumLe
    have hibv : i.toBitVec.slt 0#32 = false :=
      u32_slt_zero_of_lt_2_31 (Nat.lt_trans hiSz hlinesLt)
    have hlineBang : lines[i.toNat]! = lines[i.toNat] := by simp [hiSz]
    cases hIn : inLeaf
    · rw [hIn] at hlocs hbytes
      have hlenLt : lines[i.toNat].toByteArray.data.size < 2 ^ 31 := by
        simpa [hlineBang] using hbytesLen i.toNat hiSz
      by_cases hzero : lines[i.toNat].toByteArray.size.toUInt32 = 0
      · have hzeroB : (lines[i.toNat].toByteArray.size.toUInt32 == 0) = true := beq_iff_eq.mpr hzero
        rcases step_deserLoop_blank_line (jh := jh) (hp := hp) hlocs hiSz hibv hzero with
          ⟨k1, locs1, jh1, _, hstat1, hw15, hdl1, hstep1⟩
        have hspecEq :
            Algorithm.deserializeMacrocell.loop lines numLines i false bytes limit p col x y leaf
              nodes leaves isLeaf warns =
            Algorithm.deserializeMacrocell.loop lines numLines (i + 1) false lines[i.toNat].toByteArray
              0 0 0 0 0 0 nodes leaves isLeaf
              (if i + 1 < numLines then warns.push (.blankLine (i + 1)) else warns) := by
          rw [Algorithm.deserializeMacrocell.loop]
          simp only [hi, ↓reduceDIte, hlineBang, hzeroB, Bool.false_eq_true, ↓reduceIte]
          rw [hzero]
        rw [hspecEq]
        exact deserLoop_combine_step htest hstep1
          (deserializeMacrocell_loop_step_or_err hdl1 (hw15 hwarn15) (hstat1.trans hstat)
            hnumLe hlinesLt hbytesLen (fun h => by cases h))
      · have hzeroB : (lines[i.toNat].toByteArray.size.toUInt32 == 0) = false := beq_false_of_ne hzero
        have hlPos : 0 < lines[i.toNat].toByteArray.data.size :=
          Nat.pos_of_ne_zero fun heq0 => hzero (by simp [ByteArray.size, heq0])
        have hget0 : lines[i.toNat].toByteArray.get! 0 = lines[i.toNat].toByteArray.data[0] :=
          byteArray_get!_zero hlPos
        by_cases hb35 : lines[i.toNat].toByteArray.data[0] = 35
        · rcases step_deserLoop_comment_line (jh := jh) (hp := hp)
              hlocs hiSz hibv hzero hlPos hb35 with ⟨locs1, hw15, hdl1, hstep1⟩
          have hb35B : (lines[i.toNat].toByteArray.get! 0 == 35) = true := by
            rw [hget0, hb35]; rfl
          have hspecEq :
              Algorithm.deserializeMacrocell.loop lines numLines i false bytes limit p col x y leaf
                nodes leaves isLeaf warns =
              Algorithm.deserializeMacrocell.loop lines numLines (i + 1) false lines[i.toNat].toByteArray
                lines[i.toNat].toByteArray.size.toUInt32 0 0 0 0 0 nodes leaves isLeaf warns := by
            rw [Algorithm.deserializeMacrocell.loop]
            simp only [hi, ↓reduceDIte, hlineBang, hzeroB, Bool.false_eq_true, ↓reduceIte, hb35B]
          rw [hspecEq]
          exact deserLoop_combine_step htest hstep1
            (deserializeMacrocell_loop_step_or_err hdl1 (hw15.trans hwarn15) hstat
              hnumLe hlinesLt hbytesLen (fun h => by cases h))
        · have hb35B : (lines[i.toNat].toByteArray.get! 0 == 35) = false := by
            rw [hget0]; exact beq_false_of_ne hb35
          by_cases hdig : Algorithm.isDigitByte lines[i.toNat].toByteArray.data[0] = true
          · obtain ⟨h48, h57⟩ := (isDigitByte_iff _).mp hdig
            have hdig' : Algorithm.isDigitByte (lines[i.toNat].toByteArray.get! 0) = true := by
              rw [hget0]; exact hdig
            cases hparse : Algorithm.parseMCNodeLine lines[i.toNat].toByteArray with
            | none =>
              rcases deserLoop_parseNode_none_wrap hlocs hwarn15 hstat hiSz hibv hzero hlPos h48 h57 hparse with
                ⟨locs1, _, hstep1⟩
              have hspecEq :
                  Algorithm.deserializeMacrocell.loop lines numLines i false bytes limit p col x y leaf
                    nodes leaves isLeaf warns =
                  ⟨.unexpectedInput lines[i.toNat] i, warns.toArray, Algorithm.emptyLevel4⟩ := by
                rw [Algorithm.deserializeMacrocell.loop]
                simp only [hi, ↓reduceDIte, hlineBang, hzeroB, Bool.false_eq_true, ↓reduceIte,
                  hb35B, hdig', hparse]
              rw [hspecEq]
              exact Or.inl (deserLoop_finish_err htest hstep1 (by dsimp; intro h0; cases h0))
            | some nl =>
              cases hres : parseNodeStepResult lines[i.toNat] i nl nodes leaves isLeaf warns with
              | inl st =>
                rcases st with ⟨nodes', leaves', isLeaf'⟩
                have hspecEq :
                    Algorithm.deserializeMacrocell.loop lines numLines i false bytes limit p col x y leaf
                      nodes leaves isLeaf warns =
                    Algorithm.deserializeMacrocell.loop lines numLines (i + 1) false lines[i.toNat].toByteArray
                      lines[i.toNat].toByteArray.size.toUInt32 0 0 0 0 0 nodes' leaves' isLeaf' warns := by
                  rw [deserLoop_parseNode_specEq hi hiSz hzeroB hb35B hdig' hparse, hres]
                rw [hspecEq]
                rcases deserLoop_parseNode_some_inl hlocs hwarn15 hstat hiSz hibv hzero hlPos h48 h57 hparse hres with
                  ⟨k1, locs1, jh3, hw15, hdl1, hst3, hstep1⟩
                exact deserLoop_combine_step htest hstep1
                  (deserializeMacrocell_loop_step_or_err hdl1 hw15 hst3
                    hnumLe hlinesLt hbytesLen (fun h => by cases h))
              | inr errRes =>
                have hspecEq :
                    Algorithm.deserializeMacrocell.loop lines numLines i false bytes limit p col x y leaf
                      nodes leaves isLeaf warns = errRes := by
                  rw [deserLoop_parseNode_specEq hi hiSz hzeroB hb35B hdig' hparse, hres]
                rw [hspecEq]
                rcases deserLoop_parseNode_some_inr hlocs hwarn15 hstat hiSz hibv hzero hlPos h48 h57 hparse hres with
                  ⟨k1, pc', locs1, _, hstep1⟩
                exact Or.inl (deserLoop_finish_err htest hstep1 (parseNodeStepResult_inr_ne_ok hres))
          · have hdigF : Algorithm.isDigitByte (lines[i.toNat].toByteArray.get! 0) = false := by
              rw [hget0]; exact Bool.eq_false_iff.mpr hdig
            have hnd : lines[i.toNat].toByteArray.data[0] < 48 ∨
                (57 : UInt8) < lines[i.toNat].toByteArray.data[0] :=
              Classical.byContradiction fun hnot => hdig ((isDigitByte_iff _).mpr (not_or.mp hnot))
            rcases step_deserLoop_nondigit_line (jh := jh) (hp := hp)
                hlocs hiSz hibv hzero hlPos hb35 hnd with ⟨k1, locs1, hw15, hdl1, hstep1⟩
            have hspecEq :
                Algorithm.deserializeMacrocell.loop lines numLines i false bytes limit p col x y leaf
                  nodes leaves isLeaf warns =
                Algorithm.deserializeMacrocell.loop lines numLines i true lines[i.toNat].toByteArray
                  lines[i.toNat].toByteArray.size.toUInt32 0 0 0 0 0 nodes leaves isLeaf warns := by
              rw [Algorithm.deserializeMacrocell.loop]
              simp only [hi, ↓reduceDIte, hlineBang, hzeroB, Bool.false_eq_true, ↓reduceIte,
                hb35B, hdigF]
            rw [hspecEq]
            have hbytes1 : true = true →
                ((jh.alloc (.byteArray lines[i.toNat].toByteArray.data)).2).get? jh.objects.size =
                  some (.byteArray lines[i.toNat].toByteArray.data) ∧
                lines[i.toNat].toByteArray.size.toUInt32 = lines[i.toNat].toByteArray.size.toUInt32 ∧
                lines[i.toNat].toByteArray.data.size < 2 ^ 31 ∧
                (0 : UInt32).toNat ≤ lines[i.toNat].toByteArray.size.toUInt32.toNat :=
              fun _ => ⟨jvmHeap_get?_alloc_self _ _, rfl, hlenLt, Nat.zero_le _⟩
            exact deserLoop_combine_step htest hstep1
              (deserializeMacrocell_loop_step_or_err hdl1 (hw15.trans hwarn15) hstat
                hnumLe hlinesLt hbytesLen hbytes1)
    · rw [hIn] at hlocs hbytes
      obtain ⟨hgetBytes, hlimEq, hbytesLt, hpLe⟩ := hbytes rfl
      by_cases hpLt : p < limit
      · have hnext := Algorithm.decodeCharAt_next bytes p limit hpLt
        have hchar := step_deserLoop_leaf_char (jh := jh) (hp := hp) hlocs hgetBytes hpLt hiSz hibv
        by_cases hdollar : (Algorithm.decodeCharAt bytes p limit).1 = 36
        · have hdb : ((Algorithm.decodeCharAt bytes p limit).1 == 36) = true := beq_iff_eq.mpr hdollar
          dsimp only at hchar
          change if ((Algorithm.decodeCharAt bytes p limit).1 == 36) then _ else _ at hchar
          simp only [hdb, ↓reduceIte] at hchar
          rcases hchar with ⟨locs1, hw15, hdl1, hstep1⟩
          have hspecEq :
              Algorithm.deserializeMacrocell.loop lines numLines i true bytes limit
                p col x y leaf nodes leaves isLeaf warns =
              Algorithm.deserializeMacrocell.loop lines numLines i true bytes limit
                (Algorithm.decodeCharAt bytes p limit).2 (col + 1) 0 (y + 1) leaf
                nodes leaves isLeaf warns := by
            rw [Algorithm.deserializeMacrocell.loop]
            simp only [hi, ↓reduceDIte, hpLt, hdb, ↓reduceIte]
          rw [hspecEq]
          exact deserLoop_combine_step htest hstep1
            (deserializeMacrocell_loop_step_or_err hdl1 (hw15.trans hwarn15) hstat
              hnumLe hlinesLt hbytesLen (fun _ => ⟨hgetBytes, hlimEq, hbytesLt, hnext.2⟩))
        · have hdb : ((Algorithm.decodeCharAt bytes p limit).1 == 36) = false := beq_false_of_ne hdollar
          dsimp only at hchar
          change if ((Algorithm.decodeCharAt bytes p limit).1 == 36) then _ else _ at hchar
          simp only [hdb, Bool.false_eq_true, ↓reduceIte] at hchar
          rcases hchar with ⟨k1, locs1, jh1, hext1, hstat1, hw15, hdl1, hstep1⟩
          have hspecEq :
              Algorithm.deserializeMacrocell.loop lines numLines i true bytes limit
                p col x y leaf nodes leaves isLeaf warns =
              Algorithm.deserializeMacrocell.loop lines numLines i true bytes limit
                (Algorithm.decodeCharAt bytes p limit).2 (col + 1) (x + 1) y
                (if (Algorithm.decodeCharAt bytes p limit).1 == 42 && x < 8 && y < 8
                  then Algorithm.leafWithCell leaf x y true else leaf)
                nodes leaves isLeaf
                (if (Algorithm.decodeCharAt bytes p limit).1 != 46 &&
                    (Algorithm.decodeCharAt bytes p limit).1 != 42
                  then warns.push (.unexpectedInput i col lines[i.toNat]) else warns) := by
            rw [Algorithm.deserializeMacrocell.loop]
            simp only [hi, ↓reduceDIte, hpLt, hdb, Bool.false_eq_true, ↓reduceIte, hlineBang]
          rw [hspecEq]
          exact deserLoop_combine_step htest hstep1
            (deserializeMacrocell_loop_step_or_err hdl1 (hw15 hwarn15) (hstat1.trans hstat)
              hnumLe hlinesLt hbytesLen
              (fun _ => ⟨hext1 bytesAddr _ hgetBytes, hlimEq, hbytesLt, hnext.2⟩))
      · rcases step_deserLoop_leaf_end (jh := jh) (hp := hp) hlocs hpLt with ⟨locs1, hw15, hdl1, hstep1⟩
        have hspecEq :
            Algorithm.deserializeMacrocell.loop lines numLines i true bytes limit
              p col x y leaf nodes leaves isLeaf warns =
            Algorithm.deserializeMacrocell.loop lines numLines (i + 1) false bytes limit
              0 0 0 0 0 (nodes.push (Algorithm.makeLevel4Node leaf 0 0 0)) (leaves.push leaf)
              (isLeaf.push true) warns := by
          rw [Algorithm.deserializeMacrocell.loop]
          simp only [hi, ↓reduceDIte, hpLt, ite_true]
        rw [hspecEq]
        exact deserLoop_combine_step htest hstep1
          (deserializeMacrocell_loop_step_or_err hdl1 (hw15.trans hwarn15) hstat
            hnumLe hlinesLt hbytesLen (fun h => by cases h))
  · rw [Algorithm.deserializeMacrocell.loop]
    simp only [hi, ↓reduceDIte]
    exact Or.inr ⟨0, i, inLeaf, bytesAddr, limit, p, col, x, y, leaf, nodes, leaves, isLeaf, warns, locs, jh,
      hi, hlocs, hwarn15, hstat, by split <;> rfl, fun _ => rfl⟩
termination_by (numLines.toNat - i.toNat) * 2 ^ 33 + (if inLeaf then limit.toNat - p.toNat else 2 ^ 32)
decreasing_by
  all_goals
    simp only [hIn, Bool.false_eq_true, ite_true, ite_false]
    first
      | (have h1 := UInt32.lt_iff_toNat_lt.mp hi; omega)
      | (have := UInt32.toNat_lt (lines[i.toNat].toByteArray.size.toUInt32); omega)
      | (have := hnext.1; omega)
      | (have h1 := UInt32.lt_iff_toNat_lt.mp hi; have := UInt32.toNat_lt limit; omega)

end Algorithm.JvmVerification
