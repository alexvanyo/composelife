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

import Lean
import Std.Tactic.BVDecide
import Jvm.FastExec
import JvmSemantics
import JvmBytecode

namespace Geometry.JvmVerification

open Geometry.JvmBytecode Lean Elab Tactic Meta

theorem absFloat_closed0_equiv :
    runJvm 5 f_Geometry_absFloat___closed__0_prog (initJvmState []) =
      some (.f64 0.0) := by
  rfl

theorem absFloat_equiv (x : Float) :
    runJvm 15 f_Geometry_absFloat_prog (initJvmState [(0, .f64 x)]) =
      some (.f64 (Geometry.absFloat x)) := by
  change some (JvmVal.f64 _) = some (JvmVal.f64 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asF64, setLocal, initJvmState, Jvm.initJvmState, List.foldl, Geometry.absFloat]
  by_cases hlt : x < 0.0
  · simp [hlt]
  · by_cases heq : (x == 0.0) = true <;> simp [hlt, heq]

theorem absInt_equiv (x : Int32) :
    runJvm 15 f_Geometry_absInt_prog (initJvmState [(0, .i32 x.toUInt32)]) =
      some (.i32 (Geometry.absInt x)) := by
  rfl

section Helpers

private theorem get?_some_lt {Ext : Type} {h : Jvm.JvmHeap Ext} {addr : Nat} {obj : Jvm.HeapObj Ext}
    (hget : h.get? addr = some obj) : addr < h.objects.size := by
  simp only [Jvm.JvmHeap.get?] at hget
  exact Classical.byContradiction fun hge => by
    have hnone : h.objects[addr]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hge)
    rw [hnone] at hget
    contradiction

private theorem get?_alloc_self {Ext : Type} (h : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext) :
    (h.alloc obj).2.get? (h.alloc obj).1 = some obj := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]

private theorem get?_alloc_old {Ext : Type} (h : Jvm.JvmHeap Ext) (newObj : Jvm.HeapObj Ext)
    {addr : Nat} {oldObj : Jvm.HeapObj Ext} (hget : h.get? addr = some oldObj) :
    (h.alloc newObj).2.get? addr = some oldObj := by
  have hlt := get?_some_lt hget
  have hne : addr ≠ h.objects.size := Nat.ne_of_lt hlt
  simp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, Array.getElem?_push, hne, ↓reduceIte]
  exact hget

private theorem alloc_fst_lt {Ext : Type} (h : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext) :
    (h.alloc obj).1 < (h.alloc obj).2.objects.size := by
  simp [Jvm.JvmHeap.alloc]

private theorem get?_set_self {Ext : Type} (h : Jvm.JvmHeap Ext) (addr : Nat) (obj : Jvm.HeapObj Ext)
    (hlt : addr < h.objects.size) :
    (h.set addr obj).get? addr = some obj := by
  simp [Jvm.JvmHeap.set, hlt, Jvm.JvmHeap.get?]

private theorem int32_toUInt32_toBitVec (x : Int32) : x.toUInt32.toBitVec = x.toBitVec := by
  cases x; rfl

private theorem int32_slt_zero (x : Int32) :
    (0#32).slt x.toUInt32.toBitVec = decide ((0 : Int32) < x) := by
  rw [int32_toUInt32_toBitVec]
  by_cases h : (0 : Int32) < x
  · have : (0#32).slt x.toBitVec = true := by simpa [Int32.lt_iff_toBitVec_slt] using h
    simp [h, this]
  · have : (0#32).slt x.toBitVec = false := by
      rw [Bool.eq_false_iff]; intro hslt
      exact h (by simpa [Int32.lt_iff_toBitVec_slt] using hslt)
    simp [h, this]

private theorem int32_toUInt32_add (x y : Int32) :
    x.toUInt32 + y.toUInt32 = (x + y).toUInt32 := by
  rcases x with ⟨⟨a⟩⟩; rcases y with ⟨⟨b⟩⟩; rfl

private theorem int32_toUInt32_sub (x y : Int32) :
    x.toUInt32 - y.toUInt32 = (x - y).toUInt32 := by
  rcases x with ⟨⟨a⟩⟩; rcases y with ⟨⟨b⟩⟩; rfl

private theorem int32_beq_toUInt32 (x y : Int32) :
    (x.toUInt32 == y.toUInt32) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x.toUInt32 ≠ y.toUInt32 := by
      intro heq; apply h; cases x; cases y; cases heq; rfl
    rw [beq_false_of_ne hne, beq_false_of_ne h]

private theorem ui32_slt_zero_of_lt (n : Nat) (hlt : n < 2 ^ 31) :
    (UInt32.ofNat n).toBitVec.slt 0#32 = false := by
  rw [BitVec.slt_eq_ult, BitVec.msb_zero]
  have hm : (UInt32.ofNat n).toBitVec.msb = false := by
    rw [BitVec.msb_eq_toNat]
    have ht : (UInt32.ofNat n).toBitVec.toNat = n := by
      change (UInt32.ofNat n).toNat = n
      exact Nat.mod_eq_of_lt (by omega)
    rw [ht]
    exact decide_eq_false (by omega)
  simp [hm, BitVec.ult]

private theorem ui32_ofNat_toNat_of_lt (n : Nat) (hlt : n < 2 ^ 31) :
    (UInt32.ofNat n).toNat = n :=
  Nat.mod_eq_of_lt (by omega)

private theorem dcmpg_slt_zero (a b : Float) :
    (if (a < b) = true then (4294967295 : UInt32) else if (a == b) = true then 0 else 1).toBitVec.slt 0#32 =
      decide (a < b) := by
  by_cases hlt : a < b <;> by_cases heq : (a == b) = true <;> simp [hlt, heq]

private theorem dcmpg_sle_zero (a b : Float) :
    (if (a < b) = true then (4294967295 : UInt32) else if (a == b) = true then 0 else 1).toBitVec.sle 0#32 =
      decide (a ≤ b) := by
  rw [Jvm.float_le_eq_lt_or_beq]
  by_cases hlt : a < b <;> by_cases heq : (a == b) = true <;> simp [hlt, heq]

private theorem encodeCoordPairs_push (xs : Array (Int32 × Int32)) (x y : Int32) :
    let copied : Array JvmVal := Array.ofFn (n := xs.size + 1)
      (fun i => if h : i.val < (encodeCoordPairs xs).size then (encodeCoordPairs xs)[i.val] else .null)
    copied.set xs.size (.pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32))
      (by rw [Array.size_ofFn]; omega) = encodeCoordPairs (xs.push (x, y)) := by
  dsimp only
  apply Array.ext
  · simp [encodeCoordPairs]
  · intro i hi1 hi2
    rw [Array.getElem_set]
    by_cases heq : xs.size = i
    · subst heq
      simp only [↓reduceIte, encodeCoordPairs, Array.map_push]
      rw [Array.getElem_push]
      simp [Array.size_map]
    · simp only [heq, ↓reduceIte, Array.getElem_ofFn, encodeCoordPairs]
      have hi_lt : i < xs.size := by
        have h1 := hi1
        simp only [Array.size_set, Array.size_ofFn] at h1
        omega
      simp only [Array.size_map, hi_lt, ↓reduceDIte, Array.getElem_map, Array.map_push]
      rw [Array.getElem_push]
      simp [Array.size_map, hi_lt]

private theorem decodeCoordArray_encodeCoordPairs (xs : Array (Int32 × Int32)) :
    decodeCoordArray (encodeCoordPairs xs) = some xs := by
  simp only [decodeCoordArray, encodeCoordPairs]
  have hmap : Array.map (fun x : Int32 × Int32 =>
      (JvmVal.pair (.boxedInt x.1.toUInt32) (.boxedInt x.2.toUInt32) : JvmVal)) xs =
      ((xs.toList.map fun x : Int32 × Int32 =>
        (JvmVal.pair (.boxedInt x.1.toUInt32) (.boxedInt x.2.toUInt32) : JvmVal)).toArray) := by
    apply Array.ext'
    simp [Array.toList_map]
  rw [hmap, List.mapM_toArray, List.mapM_map]
  have h1 : (decodeCoordPair ∘ fun x : Int32 × Int32 =>
      (JvmVal.pair (.boxedInt x.1.toUInt32) (.boxedInt x.2.toUInt32) : JvmVal)) = some := by
    funext ⟨a, b⟩
    change decodeCoordPair (JvmVal.pair (.boxedInt a.toUInt32) (.boxedInt b.toUInt32)) = some (a, b)
    simp only [decodeCoordPair, Option.some.injEq, Prod.mk.injEq]
    exact ⟨rfl, rfl⟩
  rw [h1]
  have h2 : ∀ (l acc : List (Int32 × Int32)),
      List.mapM.loop (m := Option) some l acc = some (acc.reverse ++ l) := by
    intro l
    induction l with
    | nil => intro acc; simp [List.mapM.loop]
    | cons hd tl ih =>
      intro acc
      change List.mapM.loop some tl (hd :: acc) = some (acc.reverse ++ hd :: tl)
      rw [ih (hd :: acc)]
      simp
  change List.toArray <$> List.mapM.loop some xs.toList [] = some xs
  rw [h2 xs.toList []]
  simp

private theorem rayMarchLoop_dx_dy_irrel (fuel : UInt32) (startX startY dx dy dx' dy' absDx absDy : Float)
    (stepX stepY endX endY curX curY : Int32) (acc : Array (Int32 × Int32)) :
    Geometry.rayMarchLoop fuel startX startY dx dy absDx absDy stepX stepY endX endY curX curY acc =
      Geometry.rayMarchLoop fuel startX startY dx' dy' absDx absDy stepX stepY endX endY curX curY acc := by
  suffices h : ∀ n fuel curX curY acc, fuel.toNat ≤ n →
      Geometry.rayMarchLoop fuel startX startY dx dy absDx absDy stepX stepY endX endY curX curY acc =
        Geometry.rayMarchLoop fuel startX startY dx' dy' absDx absDy stepX stepY endX endY curX curY acc by
    exact h fuel.toNat fuel curX curY acc (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro fuel curX curY acc hn
    have hf0 : fuel = 0 := UInt32.toNat.inj (by have : (0 : UInt32).toNat = 0 := rfl; omega)
    subst hf0
    rw [Geometry.rayMarchLoop.eq_1, Geometry.rayMarchLoop.eq_1 (dx := dx')]
    simp
  | succ n ih =>
    intro fuel curX curY acc hn
    rw [Geometry.rayMarchLoop.eq_1, Geometry.rayMarchLoop.eq_1 (dx := dx')]
    by_cases h0 : (fuel == 0) = true
    · simp [h0]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      have hne : fuel ≠ 0 := fun hz => by subst hz; simp at h0
      have hpos : 0 < fuel.toNat := Nat.pos_of_ne_zero fun hz => hne (UInt32.toNat.inj hz)
      have hsub : (fuel - 1).toNat ≤ n := by
        rw [UInt32.toNat_sub]
        have hlt := UInt32.toNat_lt fuel
        have h1 : (1 : UInt32).toNat = 1 := rfl
        rw [h1]
        have : 2 ^ 32 - 1 + fuel.toNat = 2 ^ 32 + (fuel.toNat - 1) := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        omega
      have hih : ∀ cx cy a,
          Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY cx cy a =
          Geometry.rayMarchLoop (fuel - 1) startX startY dx' dy' absDx absDy stepX stepY endX endY cx cy a :=
        fun cx cy a => ih (fuel - 1) cx cy a hsub
      by_cases hc : ((curX == endX) && (curY == endY)) = true
      · simp [hc]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        by_cases hsx : (stepX == 0) = true
        · simp only [hsx, ↓reduceIte]
          congr 1; exact hih _ _ _
        · simp only [hsx, Bool.false_eq_true, ↓reduceIte]
          by_cases hsy : (stepY == 0) = true
          · simp only [hsy, ↓reduceIte]
            congr 1; exact hih _ _ _
          · simp only [hsy, Bool.false_eq_true, ↓reduceIte]
            congr 1; exact hih _ _ _

end Helpers

section ChunkExec

private def isGeoStop (instr : JvmInstr) : Bool :=
  Jvm.isBranchInstr instr ||
    match instr with
    | .invokestatic _ _ _ | .invokespecial _ _ _ | .newClass _ | .anewarray _
    | .arraylength | .aastore | .checkcast _ | .i2l | .dcmpg | .dcmpl => true
    | _ => false

private def stepGeoChunk :
    Nat → Nat → Nat → List JvmInstr → JvmState → Jvm.BlockResChunkRes Empty Unit
  | _, 0, _, _, _ => .done none
  | 0, f1 + 1, pc, instrs, st => .cont (f1 + 1) pc instrs st
  | m + 1, f1 + 1, pc, instrs, st =>
    match instrs with
    | [] => .done none
    | instr :: rest =>
      if isGeoStop instr then .cont (f1 + 1) pc (instr :: rest) st
      else match Jvm.stepInstr geomHooks instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepGeoChunk m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr (some v) => .done (some (v, { st with pc := pc }))
        | .inr none => .done none

private theorem runJvmResFast_stepGeoChunk (m f1 pc : Nat) (prog instrs : List JvmInstr)
    (st : JvmState) (hdrop : prog.drop pc = instrs) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc instrs st =
      Jvm.afterResBlockChunk geomHooks (stepGeoChunk m (f1 + 1) pc instrs st) prog := by
  induction m generalizing f1 pc instrs st with
  | zero => simp [stepGeoChunk, Jvm.afterResBlockChunk]
  | succ m ih =>
    cases instrs with
    | nil => simp [stepGeoChunk, Jvm.afterResBlockChunk, Jvm.runJvmResFast]
    | cons instr rest =>
      dsimp only [stepGeoChunk]
      by_cases hstop : isGeoStop instr = true
      · simp [hstop, Jvm.afterResBlockChunk]
      · have hnotbr : Jvm.isBranchInstr instr = false := by
          cases hbr : Jvm.isBranchInstr instr with
          | false => rfl
          | true =>
            have : isGeoStop instr = true := by simp [isGeoStop, hbr]
            simp [this] at hstop
        have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') := by
          rintro ⟨rfl, _⟩
          have : isGeoStop .i2l = true := rfl
          simp [this] at hstop
        rw [Jvm.runJvmResFast_step_nonbranch geomHooks f1 prog pc instr rest st hnotbr hno']
        simp only [hstop, Bool.false_eq_true, ↓reduceIte]
        cases hstep : Jvm.stepInstr geomHooks instr { st with pc := pc } with
        | inr res => cases res <;> simp [Jvm.afterResBlockChunk]
        | inl ost =>
          cases ost with
          | none => simp [Jvm.afterResBlockChunk]
          | some st' =>
            by_cases hpc : st'.pc = pc + 1
            · simp only [hpc, ↓reduceIte]
              have hdrop' : prog.drop (pc + 1) = rest := by
                have := congrArg List.tail hdrop
                simpa [List.tail_drop] using this
              cases f1 with
              | zero => simp [stepGeoChunk, Jvm.afterResBlockChunk, Jvm.runJvmResFast]
              | succ f2 => exact ih f2 (pc + 1) rest st' hdrop'
            · simp only [hpc, ↓reduceIte, Jvm.afterResBlockChunk]

private theorem runJvmResFast_stepGeo_step {f pc pc' : Nat} {prog : List JvmInstr}
    {instr : JvmInstr} {rest : List JvmInstr} {stk stk' : List JvmVal}
    {locs locs' : Nat → JvmVal} {jh jh' : Jvm.JvmHeap Empty} {hp hp' : Unit}
    (hstep : Jvm.stepInstr geomHooks instr
        { pc := pc, stack := stk, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc', stack := stk', locals := locs', jvmHeap := jh', heap := hp' }))
    (hnbr : Jvm.isBranchInstr instr = false)
    (hnoi2l : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r'))
    (hpc : pc' = pc + 1) :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (instr :: rest)
        { pc := pc, stack := stk, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        { pc := pc', stack := stk', locals := locs', jvmHeap := jh', heap := hp' } := by
  have h1 := Jvm.runJvmResFast_step_nonbranch geomHooks f prog pc instr rest
    { pc := pc, stack := stk, locals := locs, jvmHeap := jh, heap := hp } hnbr hnoi2l
  change _ = _ at h1
  rw [h1]
  dsimp only
  rw [hstep]
  simp [hpc]

private theorem step_absFloat_closed0 {pc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.invokestatic "LineSegmentLeanKt" "f_Geometry_absFloat___closed__0" "()D")
        { pc := pc, stack := stk, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .f64 0.0 :: stk, locals := locs, jvmHeap := jh, heap := hp }) := rfl

private theorem step_absFloat {pc : Nat} {x : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.invokestatic "LineSegmentLeanKt" "f_Geometry_absFloat" "(D)D")
        { pc := pc, stack := x :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .f64 (Geometry.absFloat (JvmVal.asF64 x)) :: rest,
                   locals := locs, jvmHeap := jh, heap := hp }) := rfl

private theorem step_absInt {pc : Nat} {x : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.invokestatic "LineSegmentLeanKt" "f_Geometry_absInt" "(I)I")
        { pc := pc, stack := x :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .i32 (Geometry.absInt (JvmVal.asI32 x).toInt32) :: rest,
                   locals := locs, jvmHeap := jh, heap := hp }) := rfl

private theorem step_rayMarchLoop_call {pc accAddr : Nat}
    {curY curX endY endX stepY stepX absDy absDx startY startX fuel : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    {cls : String} {elems : Array JvmVal} {acc : Array (Int32 × Int32)}
    (hheap : jh.get? accAddr = some (.objArray cls elems))
    (hdec : decodeCoordArray elems = some acc) :
    Jvm.stepInstr geomHooks
        (.invokestatic "LineSegmentLeanKt" "f_Geometry_rayMarchLoop___redArg-v0ARYG8"
          "(IDDDDIIIIIILjava/lang/Object;)Ljava/lang/Object;")
        { pc := pc,
          stack := .heapRef accAddr :: curY :: curX :: endY :: endX :: stepY :: stepX ::
            absDy :: absDx :: startY :: startX :: fuel :: rest,
          locals := locs, jvmHeap := jh, heap := hp } =
      let out := Geometry.rayMarchLoop
        (JvmVal.asI32 fuel) (JvmVal.asF64 startX) (JvmVal.asF64 startY) 0.0 0.0
        (JvmVal.asF64 absDx) (JvmVal.asF64 absDy)
        (JvmVal.asI32 stepX).toInt32 (JvmVal.asI32 stepY).toInt32
        (JvmVal.asI32 endX).toInt32 (JvmVal.asI32 endY).toInt32
        (JvmVal.asI32 curX).toInt32 (JvmVal.asI32 curY).toInt32 acc
      let res := jh.alloc (.objArray cls (encodeCoordPairs out))
      .inl (some { pc := pc + 1, stack := .heapRef res.1 :: rest, locals := locs, jvmHeap := res.2, heap := hp }) := by
  change (match jh.get? accAddr with
    | some (.objArray cls elems) => _
    | _ => _) = _
  rw [hheap]; dsimp only; rw [hdec]

private def geoDcmpg (a b : Float) : UInt32 :=
  if a < b then 4294967295 else if a == b then 0 else 1

private theorem step_dcmpg {pc : Nat} {a b : Float} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks .dcmpg
        { pc := pc, stack := .f64 b :: .f64 a :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .i32 (geoDcmpg a b) :: rest,
                   locals := locs, jvmHeap := jh, heap := hp }) := by
  dsimp [Jvm.stepInstr, geoDcmpg, Jvm.JvmVal.asF64]
  by_cases heq : a == b
  · by_cases hlt : a < b <;> simp [heq, hlt]
    -- a == b and a < b is possible? wait for Float, check both branches!
  · by_cases hlt : a < b <;> simp [heq, hlt]

private theorem step_newClass_pair {pc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.newClass "kotlin/Pair")
        { pc := pc, stack := stk, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .allocRef "kotlin/Pair" :: stk,
                   locals := locs, jvmHeap := jh, heap := hp }) := by
  dsimp [Jvm.stepInstr, geomHooks]

private theorem step_pair_init {pc : Nat} {a b : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks
        (.invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V")
        { pc := pc, stack := b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: rest,
          locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .pair a b :: rest,
                   locals := locs, jvmHeap := jh, heap := hp }) := by
  simp [Jvm.stepInstr, Jvm.stepInvokeSpecialGeneric]

private theorem step_integer_valueOf {pc : Nat} {v : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;")
        { pc := pc, stack := v :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .boxedInt (JvmVal.asI32 v) :: rest,
                   locals := locs, jvmHeap := jh, heap := hp }) := rfl

private theorem step_uint_ctor {pc : Nat} {v : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.invokestatic "kotlin/UInt" "constructor-impl" "(I)I")
        { pc := pc, stack := v :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := v :: rest, locals := locs, jvmHeap := jh, heap := hp }) := rfl

private theorem step_intrinsics_checkNotNull {pc addr : Nat} {msg : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
        { pc := pc, stack := msg :: .heapRef addr :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := rest, locals := locs, jvmHeap := jh, heap := hp }) := rfl

private theorem step_intrinsics_checkNotNullExpr {pc addr : Nat} {msg : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.stepInstr geomHooks (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
        { pc := pc, stack := msg :: .heapRef addr :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := rest, locals := locs, jvmHeap := jh, heap := hp }) := rfl

private theorem step_arrays_copyOf {pc addr : Nat} {newLen : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    {elemCls : String} {elems : Array JvmVal}
    (hnonneg : newLen.toBitVec.slt 0#32 = false)
    (hheap : jh.get? addr = some (.objArray elemCls elems)) :
    Jvm.stepInstr geomHooks (.invokestatic "java/util/Arrays" "copyOf"
        "([Ljava/lang/Object;I)[Ljava/lang/Object;")
        { pc := pc, stack := .i32 newLen :: .heapRef addr :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      let n := newLen.toNat
      let copied := Array.ofFn (n := n) (fun i => if h : i.val < elems.size then elems[i.val] else .null)
      let res := jh.alloc (.objArray elemCls copied)
      .inl (some { pc := pc + 1, stack := .heapRef res.1 :: rest, locals := locs, jvmHeap := res.2, heap := hp }) := by
  change (if (JvmVal.asI32 (.i32 newLen)).toBitVec.slt 0#32 = true then _ else _) = _
  have hnn : (JvmVal.asI32 (Ext := Empty) (.i32 newLen)).toBitVec.slt 0#32 = false := hnonneg
  rw [ite_eq_right_iff.mpr (fun ht => by simp [hnn] at ht), hheap]
  rfl

private theorem step_anewarray {pc : Nat} {cls : String} {len : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (hnonneg : len.toBitVec.slt 0#32 = false) :
    Jvm.stepInstr geomHooks (.anewarray cls)
        { pc := pc, stack := .i32 len :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      let res := jh.alloc (.objArray cls (Array.replicate len.toNat .null))
      .inl (some { pc := pc + 1, stack := .heapRef res.1 :: rest, locals := locs, jvmHeap := res.2, heap := hp }) := by
  change (if (JvmVal.asI32 (.i32 len)).toBitVec.slt 0#32 = true then _ else _) = _
  have hnn : (JvmVal.asI32 (Ext := Empty) (.i32 len)).toBitVec.slt 0#32 = false := hnonneg
  rw [ite_eq_right_iff.mpr (fun ht => by simp [hnn] at ht)]
  rfl

private theorem step_arraylength {pc addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    {cls : String} {elems : Array JvmVal}
    (hheap : jh.get? addr = some (.objArray cls elems)) :
    Jvm.stepInstr geomHooks .arraylength
        { pc := pc, stack := .heapRef addr :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest,
                   locals := locs, jvmHeap := jh, heap := hp }) := by
  change (match jh.get? addr >>= Jvm.HeapObj.arrayLength? with
    | some len => _
    | none => _) = _
  rw [hheap]
  rfl

private theorem step_checkcast_objArray {pc addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    {elemCls : String} {elems : Array JvmVal}
    (hheap : jh.get? addr = some (.objArray elemCls elems)) :
    Jvm.stepInstr geomHooks (.checkcast "[Ljava/lang/Object;")
        { pc := pc, stack := .heapRef addr :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some { pc := pc + 1, stack := .heapRef addr :: rest,
                   locals := locs, jvmHeap := jh, heap := hp }) := by
  simp [Jvm.stepInstr, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, hheap, Jvm.HeapObj.matchesType]

private theorem step_aastore {pc addr : Nat} {val : JvmVal} {idx : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    {cls : String} {elems : Array JvmVal}
    (hnonneg : idx.toBitVec.slt 0#32 = false)
    (hheap : jh.get? addr = some (.objArray cls elems))
    (hlt : idx.toNat < elems.size) :
    Jvm.stepInstr geomHooks .aastore
        { pc := pc, stack := val :: .i32 idx :: .heapRef addr :: rest, locals := locs, jvmHeap := jh, heap := hp } =
      .inl (some {
        pc := pc + 1
        stack := rest
        locals := locs
        jvmHeap := jh.set addr (.objArray cls (elems.set idx.toNat val hlt))
        heap := hp
      }) := by
  change (if (JvmVal.asI32 (.i32 idx)).toBitVec.slt 0#32 = true then _ else _) = _
  have hnn : (JvmVal.asI32 (Ext := Empty) (.i32 idx)).toBitVec.slt 0#32 = false := hnonneg
  rw [ite_eq_right_iff.mpr (fun ht => by simp [hnn] at ht), hheap]
  simp only [JvmVal.asI32, hlt, ↓reduceDIte]

private def geoBlkOpaque : NameSet :=
  List.foldl NameSet.insert {} [
    `OfScientific.ofScientific, `Float.ofScientific,
    `Float.sub, `Float.mul, `Float.add, `Float.div, `Float.abs, `Float.neg,
    `Float.lt, `Float.le, `Float.beq,
    `instBEqFloat, `instLTFloat, `instLEFloat,
    `Int32.toFloat, `Int32.toUInt32, `Int32.sub, `Int32.add,
    `UInt32.toInt32, `UInt32.ofBitVec, `UInt32.toBitVec, `UInt32.ofNat,
    `UInt32.add, `UInt32.sub,
    `Geometry.absFloat, `Geometry.absInt, `Geometry.rayMarchLoop,
    `BitVec.slt, `BitVec.sle,
    `Jvm.setLocal, `Jvm.JvmVal.asI32, `Jvm.JvmVal.asF64,
    `Jvm.runJvmResFast,
    `Jvm.JvmHeap.alloc, `Jvm.JvmHeap.get?, `Jvm.JvmHeap.set,
    `encodeCoordPairs, `decodeCoordArray, `Array.ofFn, `Array.set, ``geoDcmpg
  ]

private def geoWithOpaque {α : Type} (opaques : NameSet) (k : MetaM α) : MetaM α := do
  let orig ← getTransparency
  withConfig (fun cfg => { cfg with transparency := orig }) do
    Lean.Meta.withCanUnfoldPred (fun cfg c => do
      if opaques.contains c.name then return false
      else Lean.Meta.canUnfoldDefault cfg c) k

private def geoNatLit? (e : Expr) : Option Nat :=
  e.rawNatLit? <|> e.nat?

private partial def geoNormNat (e : Expr) : MetaM Expr := do
  if let some n := geoNatLit? e then
    return Lean.mkNatLit n
  let e ← geoWithOpaque geoBlkOpaque (whnf e)
  if let some n := geoNatLit? e then
    return Lean.mkNatLit n
  if e.isAppOfArity ``Nat.succ 1 then
    let a ← geoNormNat (e.getArg! 0)
    if let some n := geoNatLit? a then
      return Lean.mkNatLit (n + 1)
    return mkApp (mkConst ``Nat.succ) a
  else if e.isAppOfArity ``Nat.add 2 then
    let a ← geoNormNat (e.getArg! 0)
    let b ← geoNormNat (e.getArg! 1)
    if let (some na, some nb) := (geoNatLit? a, geoNatLit? b) then
      return Lean.mkNatLit (na + nb)
    return mkApp2 (mkConst ``Nat.add) a b
  else return e

mutual
private partial def geoNormLocalsSpine (e : Expr) : MetaM Expr := do
  let e ← geoWithOpaque geoBlkOpaque (whnf e)
  match e with
  | .app (.app (.app (.app (.const ``Jvm.setLocal us) ext) base) k) v =>
    let k' ← geoNormNat k
    return mkApp4 (.const ``Jvm.setLocal us) ext (← geoNormLocalsSpine base) k' (← geoNormExpr v)
  | .app (.app (.app (.app (.app (.const ``Jvm.setLocal us) ext) base) k) v) q =>
    let k' ← geoNormNat k
    let q' ← geoNormNat q
    match geoNatLit? k', geoNatLit? q' with
    | some kn, some qn =>
      if kn == qn then geoNormLocalsSpine v
      else
        let qNat ← Lean.Meta.mkNumeral (mkConst ``Nat) qn
        geoNormLocalsSpine (mkApp base qNat)
    | _, _ =>
      return mkApp5 (.const ``Jvm.setLocal us) ext (← geoNormLocalsSpine base) k' (← geoNormExpr v) q'
  | _ => return e

private partial def geoNormExpr (e : Expr) : MetaM Expr := do
  let e ← geoWithOpaque geoBlkOpaque (whnf e)
  if e.isAppOf ``Jvm.setLocal then
    let args := e.getAppArgs
    if args.size == 4 then
      let base' ← geoNormLocalsSpine args[1]!
      let v' ← geoNormExpr args[3]!
      return mkApp4 e.getAppFn args[0]! base' args[2]! v'
    else if args.size == 5 then
      let q' ← geoNormNat args[4]!
      let res ← geoNormLocalsSpine (mkApp5 e.getAppFn args[0]! args[1]! args[2]! args[3]! q')
      let res' ← geoWithOpaque geoBlkOpaque (whnf res)
      if res'.isAppOf ``Jvm.setLocal then return res'
      else geoNormExpr res'
    else return e
  else if e.isAppOf ``List.cons then
    let args := e.getAppArgs
    if args.size == 3 then
      return mkApp2 (mkApp e.getAppFn args[0]!) (← geoNormExpr args[1]!) (← geoNormExpr args[2]!)
    else return e
  else if e.isAppOf ``Option.some then
    let args := e.getAppArgs
    if args.size == 2 then
      return mkApp2 e.getAppFn args[0]! (← geoNormExpr args[1]!)
    else return e
  else if e.isAppOf ``Prod.mk then
    let args := e.getAppArgs
    if args.size == 4 then
      return mkApp4 e.getAppFn args[0]! args[1]! (← geoNormExpr args[2]!) (← geoNormExpr args[3]!)
    else return e
  else if e.isAppOf ``Jvm.JvmVal.f64 || e.isAppOf ``Jvm.JvmVal.i32 || e.isAppOf ``Jvm.JvmVal.boxedInt ||
      e.isAppOf ``Jvm.JvmVal.pair || e.isAppOf ``Jvm.JvmVal.heapRef then
    let fn := e.getAppFn
    let args ← e.getAppArgs.mapM geoNormExpr
    return mkAppN fn args
  else if e.isAppOf ``Jvm.JvmVal.asI32 then
    let args := e.getAppArgs
    if args.size == 2 then
      let v' ← geoNormExpr args[1]!
      if v'.isAppOfArity ``Jvm.JvmVal.i32 2 then
        return v'.getArg! 1
      else return mkApp2 e.getAppFn args[0]! v'
    else return e
  else if e.isAppOf ``Jvm.JvmVal.asF64 then
    let args := e.getAppArgs
    if args.size == 2 then
      let v' ← geoNormExpr args[1]!
      if v'.isAppOfArity ``Jvm.JvmVal.f64 2 then
        return v'.getArg! 1
      else return mkApp2 e.getAppFn args[0]! v'
    else return e
  else if e.isAppOf ``HSub.hSub || e.isAppOf ``HAdd.hAdd || e.isAppOf ``HMul.hMul || e.isAppOf ``HDiv.hDiv then
    let args := e.getAppArgs
    if args.size == 6 then
      let a' ← geoNormExpr args[4]!
      let b' ← geoNormExpr args[5]!
      return mkAppN e.getAppFn (args.set! 4 a' |>.set! 5 b')
    else return e
  else if e.isAppOf ``Neg.neg then
    let args := e.getAppArgs
    if args.size == 3 then
      return mkAppN e.getAppFn (args.set! 2 (← geoNormExpr args[2]!))
    else return e
  else if e.isAppOf ``BEq.beq || e.isAppOf ``LT.lt || e.isAppOf ``LE.le then
    let args := e.getAppArgs
    if args.size == 4 then
      let a' ← geoNormExpr args[2]!
      let b' ← geoNormExpr args[3]!
      return mkAppN e.getAppFn (args.set! 2 a' |>.set! 3 b')
    else return e
  else if e.isAppOf ``UInt32.add || e.isAppOf ``UInt32.sub ||
      e.isAppOf ``Float.add || e.isAppOf ``Float.sub || e.isAppOf ``Float.mul || e.isAppOf ``Float.div ||
      e.isAppOf ``Float.lt || e.isAppOf ``Float.le || e.isAppOf ``Float.beq then
    let args := e.getAppArgs
    if args.size == 2 then
      return mkApp2 e.getAppFn (← geoNormExpr args[0]!) (← geoNormExpr args[1]!)
    else return e
  else if e.isAppOf ``UInt32.toInt32 || e.isAppOf ``UInt32.toBitVec || e.isAppOf ``UInt32.ofBitVec ||
      e.isAppOf ``Int32.toUInt32 || e.isAppOf ``Int32.toFloat || e.isAppOf ``Float.neg ||
      e.isAppOf ``Geometry.absFloat || e.isAppOf ``Geometry.absInt then
    let args := e.getAppArgs
    if args.size == 1 then
      return mkApp e.getAppFn (← geoNormExpr args[0]!)
    else return e
  else if e.isAppOf ``ite || e.isAppOf ``dite then
    let args := e.getAppArgs
    if args.size == 5 then
      let cond ← geoNormExpr args[1]!
      let tbr ← geoNormExpr args[3]!
      let fbr ← geoNormExpr args[4]!
      return mkApp5 e.getAppFn args[0]! cond args[2]! tbr fbr
    else return e
  else if e.isAppOf ``Eq then
    let args := e.getAppArgs
    if args.size == 3 then
      return mkApp3 e.getAppFn args[0]! (← geoNormExpr args[1]!) (← geoNormExpr args[2]!)
    else return e
  else if e.isAppOf ``BitVec.slt || e.isAppOf ``BitVec.sle then
    let args := e.getAppArgs
    if args.size == 3 then
      return mkApp3 e.getAppFn args[0]! (← geoNormExpr args[1]!) (← geoNormExpr args[2]!)
    else return e
  else if e.isAppOf ``Jvm.JvmState.mk then
    let fn := e.getAppFn
    let args := e.getAppArgs
    if args.size == 7 then
      let pc' ← geoNormNat args[2]!
      let stk' ← geoNormExpr args[3]!
      let locs' ← geoNormExpr args[4]!
      let heap' ← geoNormExpr args[5]!
      let u' ← geoNormExpr args[6]!
      return mkAppN fn #[args[0]!, args[1]!, pc', stk', locs', heap', u']
    else return e
  else if e.isAppOf ``Jvm.runJvmResFast then
    let args := e.getAppArgs
    if args.size == 8 then
      let f' ← withTransparency .reducible (whnf args[3]!)
      let pc' ← geoNormNat args[5]!
      let instrs' ← geoWithOpaque geoBlkOpaque (whnf args[6]!)
      let st' ← geoNormExpr args[7]!
      return mkAppN e.getAppFn (args.set! 3 f' |>.set! 5 pc' |>.set! 6 instrs' |>.set! 7 st')
    else return e
  else return e

private partial def geoNormBranchExpr (e : Expr) : MetaM Expr := do
  let e ← geoWithOpaque (geoBlkOpaque.insert ``ite |>.insert ``dite) (whnf e)
  if e.isAppOf ``ite || e.isAppOf ``dite then
    let args := e.getAppArgs
    if args.size == 5 then
      let cond ← geoNormExpr args[1]!
      let tbr ← geoNormBranchExpr args[3]!
      let fbr ← geoNormBranchExpr args[4]!
      return mkApp5 e.getAppFn args[0]! cond args[2]! tbr fbr
    else return e
  else return ← geoNormExpr e
end

elab "geo_norm_lhs" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← g.getType
    let some (_, lhs, rhs) := tgt.eq? | throwError "geo_norm_lhs: expected equality goal"
    let lhs' ← geoNormExpr lhs
    let tgt' ← mkEq lhs' rhs
    let g' ← g.replaceTargetDefEq tgt'
    replaceMainGoal [g']

elab "geo_norm_branch_lhs" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← g.getType
    let some (_, lhs, rhs) := tgt.eq? | throwError "geo_norm_branch_lhs: expected equality goal"
    let lhs' ← geoNormBranchExpr lhs
    let tgt' ← mkEq lhs' rhs
    let g' ← g.replaceTargetDefEq tgt'
    replaceMainGoal [g']

macro "geo_chunk_n" n:term : tactic =>
  `(tactic| (
    rw [runJvmResFast_stepGeoChunk $n]
    rotate_left
    rfl
    geo_norm_lhs))

macro "geo_chunk" : tactic =>
  `(tactic| geo_chunk_n 80)

macro "geo_branch" : tactic =>
  `(tactic| (
    rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
    geo_norm_branch_lhs))

macro "geo_step" hstep:term : tactic =>
  `(tactic| (
    rw [runJvmResFast_stepGeo_step $hstep rfl (by intro ⟨h, _⟩; cases h) rfl]
    geo_norm_lhs))

private theorem id_rw {P : Prop} (h : P) : P := h

private theorem runJvmResFast_eq {f pc : Nat} {prog : List JvmInstr} {i1 i2 : List JvmInstr} {s1 s2 : JvmState}
    (hi : i1 = i2) (hs : s1 = s2) :
    Jvm.runJvmResFast geomHooks f prog pc i1 s1 =
      Jvm.runJvmResFast geomHooks f prog pc i2 s2 := by
  rw [hi, hs]

private theorem branch_goto {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.goto target :: rest)
        { pc := pc, stack := srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog target (prog.drop target)
        { pc := target, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons]

private theorem branch_goto_eq {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {srest : List JvmVal} {locs1 locs2 : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (hlocs : locs1 = locs2) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.goto target :: rest)
        { pc := pc, stack := srest, locals := locs1, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog target (prog.drop target)
        { pc := target, stack := srest, locals := locs2, jvmHeap := jh, heap := hp } := by
  subst hlocs
  exact branch_goto

macro "geo_branch_step" hbr:term : tactic =>
  `(tactic| (
    rw [id_rw $hbr]
    geo_norm_lhs))

private theorem branch_iflt_true {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : x.toBitVec.slt 0#32 = true) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.iflt target :: rest)
        { pc := pc, stack := .i32 x :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog target (prog.drop target)
        { pc := target, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

private theorem branch_iflt_false {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : x.toBitVec.slt 0#32 = false) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.iflt target :: rest)
        { pc := pc, stack := .i32 x :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog (pc + 1) rest
        { pc := pc + 1, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

private theorem branch_ifle_true {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : x.toBitVec.sle 0#32 = true) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.ifle target :: rest)
        { pc := pc, stack := .i32 x :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog target (prog.drop target)
        { pc := target, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

private theorem branch_ifle_false {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : x.toBitVec.sle 0#32 = false) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.ifle target :: rest)
        { pc := pc, stack := .i32 x :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog (pc + 1) rest
        { pc := pc + 1, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

private theorem branch_ifeq_true {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : x = 0) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.ifeq target :: rest)
        { pc := pc, stack := .i32 x :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog target (prog.drop target)
        { pc := target, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, geomHooks, Jvm.JvmVal.asI32, h]

private theorem branch_ifeq_false {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : x ≠ 0) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.ifeq target :: rest)
        { pc := pc, stack := .i32 x :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog (pc + 1) rest
        { pc := pc + 1, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, geomHooks, Jvm.JvmVal.asI32, h]

private theorem branch_if_icmpne_true {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : a ≠ b) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.if_icmpne target :: rest)
        { pc := pc, stack := .i32 b :: .i32 a :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog target (prog.drop target)
        { pc := target, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

private theorem branch_if_icmpne_false {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : a = b) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.if_icmpne target :: rest)
        { pc := pc, stack := .i32 b :: .i32 a :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog (pc + 1) rest
        { pc := pc + 1, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

private theorem branch_if_icmplt_true {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : a.toBitVec.slt b.toBitVec = true) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.if_icmplt target :: rest)
        { pc := pc, stack := .i32 b :: .i32 a :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog target (prog.drop target)
        { pc := target, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

private theorem branch_if_icmplt_false {f1 pc target : Nat} {prog : List JvmInstr} {rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (h : a.toBitVec.slt b.toBitVec = false) :
    Jvm.runJvmResFast geomHooks (f1 + 1) prog pc (.if_icmplt target :: rest)
        { pc := pc, stack := .i32 b :: .i32 a :: srest, locals := locs, jvmHeap := jh, heap := hp } =
      Jvm.runJvmResFast geomHooks f1 prog (pc + 1) rest
        { pc := pc + 1, stack := srest, locals := locs, jvmHeap := jh, heap := hp } := by
  rw [Jvm.runJvmResFast_at_branch_cons (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.JvmVal.asI32, h]

end ChunkExec

private theorem asI32_i32 (x : UInt32) : JvmVal.asI32 (Ext := Empty) (.i32 x) = x := rfl
private theorem asF64_f64 (x : Float) : JvmVal.asF64 (Ext := Empty) (.f64 x) = x := rfl
private theorem ui32_sub_eq (a b : UInt32) : a.sub b = a - b := rfl
private theorem ui32_add_eq (a b : UInt32) : a.add b = a + b := rfl

section RayMarchSegmentCoords

private theorem seg_from132 (k : Nat) (startX startY endX endY : Float)
    (startCellX startCellY endCellX endCellY : Int32) (stepX stepY : Int32)
    (locs : Nat → JvmVal)
    (h12 : locs 12 = .f64 (endY - startY))
    (h14 : locs 14 = .f64 (endX - startX))
    (h16 : locs 16 = .i32 stepX.toUInt32)
    (h17 : locs 17 = .i32 stepY.toUInt32)
    (h0 : locs 0 = .f64 startX)
    (h2 : locs 2 = .f64 startY)
    (h8 : locs 8 = .i32 startCellX.toUInt32)
    (h9 : locs 9 = .i32 startCellY.toUInt32)
    (h10 : locs 10 = .i32 endCellX.toUInt32)
    (h11 : locs 11 = .i32 endCellY.toUInt32) :
    ∃ outAddr st',
      Jvm.runJvmResFast geomHooks (k + 120) f_Geometry_rayMarchSegmentCoords_prog 132
          (f_Geometry_rayMarchSegmentCoords_prog.drop 132)
          { pc := 132, stack := [], locals := locs, jvmHeap := {}, heap := () } =
        some (.heapRef outAddr, st') ∧
      st'.jvmHeap.get? outAddr = some (.objArray "java/lang/Object" (encodeCoordPairs
        (Geometry.rayMarchLoop
          (Geometry.absInt (endCellX - startCellX) + Geometry.absInt (endCellY - startCellY) + 2)
          startX startY (endX - startX) (endY - startY)
          (Geometry.absFloat (endX - startX)) (Geometry.absFloat (endY - startY))
          stepX stepY endCellX endCellY startCellX startCellY
          #[(startCellX, startCellY), (endCellX, endCellY)]))) := by
  have hlt0 : 0 < 2 ^ 31 := by decide
  have hlt1 : 1 < 2 ^ 31 := by decide
  have hlt2 : 2 < 2 ^ 31 := by decide
  have hnn0 : (0 : UInt32).toBitVec.slt 0#32 = false := by decide
  have hnn0' : (UInt32.ofNat 0).toBitVec.slt 0#32 = false := hnn0
  have hnn1 : (UInt32.ofNat 1).toBitVec.slt 0#32 = false := ui32_slt_zero_of_lt 1 hlt1
  have hnn2 : (UInt32.ofNat 2).toBitVec.slt 0#32 = false := ui32_slt_zero_of_lt 2 hlt2
  let pair0 : JvmVal := .pair (.boxedInt startCellX.toUInt32) (.boxedInt startCellY.toUInt32)
  let pair1 : JvmVal := .pair (.boxedInt endCellX.toUInt32) (.boxedInt endCellY.toUInt32)
  let h_empty : Jvm.JvmHeap Empty := {}
  let a0 := h_empty.alloc (.objArray "java/lang/Object" (Array.replicate (UInt32.ofNat 0).toNat .null))
  have ha0 : a0.2.get? a0.1 = some (.objArray "java/lang/Object" #[]) := by
    simpa [a0] using get?_alloc_self h_empty (.objArray "java/lang/Object" #[])
  let copied1 : Array JvmVal := Array.ofFn (n := (UInt32.ofNat 1).toNat)
    (fun i => if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val] else .null)
  let a1 := a0.2.alloc (.objArray "java/lang/Object" copied1)
  have ha0_in_a1 : a1.2.get? a0.1 = some (.objArray "java/lang/Object" #[]) :=
    get?_alloc_old a0.2 _ ha0
  have ha1_self : a1.2.get? a1.1 = some (.objArray "java/lang/Object" copied1) :=
    get?_alloc_self a0.2 _
  have ha1_lt : a1.1 < a1.2.objects.size := alloc_fst_lt a0.2 _
  let h3 := a1.2.set a1.1 (.objArray "java/lang/Object" (copied1.set (UInt32.ofNat 0).toNat pair0 (by simp [copied1])))
  have hpush1 : copied1.set (UInt32.ofNat 0).toNat pair0 (by simp [copied1]) = #[pair0] := by
    apply Array.ext
    · simp [copied1]
    · intro i _ hi₂; simp only [List.size_toArray, List.length_cons, List.length_nil] at hi₂
      simp [copied1, show i = 0 by omega]
  have ha1_in_h3 : h3.get? a1.1 = some (.objArray "java/lang/Object" #[pair0]) := by
    rw [← hpush1]
    exact get?_set_self a1.2 a1.1 _ ha1_lt
  let copied2 : Array JvmVal := Array.ofFn (n := (UInt32.ofNat 2).toNat)
    (fun i => if h : i.val < (#[pair0] : Array JvmVal).size then (#[pair0] : Array JvmVal)[i.val] else .null)
  let a2 := h3.alloc (.objArray "java/lang/Object" copied2)
  have ha1_in_a2 : a2.2.get? a1.1 = some (.objArray "java/lang/Object" #[pair0]) :=
    get?_alloc_old h3 _ ha1_in_h3
  have ha2_self : a2.2.get? a2.1 = some (.objArray "java/lang/Object" copied2) :=
    get?_alloc_self h3 _
  have ha2_lt : a2.1 < a2.2.objects.size := alloc_fst_lt h3 _
  let h5 := a2.2.set a2.1 (.objArray "java/lang/Object" (copied2.set (UInt32.ofNat 1).toNat pair1 (by simp [copied2])))
  have hpush2 : copied2.set (UInt32.ofNat 1).toNat pair1 (by simp [copied2]) = #[pair0, pair1] := by
    apply Array.ext
    · simp [copied2]
    · intro i _ hi₂; simp only [List.size_toArray, List.length_cons, List.length_nil] at hi₂
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [copied2]
  have ha2_in_h5 : h5.get? a2.1 = some (.objArray "java/lang/Object" #[pair0, pair1]) := by
    rw [← hpush2]
    exact get?_set_self a2.2 a2.1 _ ha2_lt
  refine ⟨?outAddr, ?st', ?hrun, ?hget⟩
  case hrun =>
    geo_chunk
    rw [h14]
    geo_step step_absFloat
    geo_chunk
    rw [h12]
    geo_step step_absFloat
    geo_chunk
    rw [h10, h8, asI32_i32, asI32_i32, ui32_sub_eq, int32_toUInt32_sub]
    geo_step step_absInt
    geo_chunk
    rw [h11, h9, asI32_i32, asI32_i32, ui32_sub_eq, int32_toUInt32_sub]
    geo_step step_absInt
    geo_chunk
    geo_step step_uint_ctor
    geo_chunk
    geo_step step_uint_ctor
    geo_chunk
    geo_step step_newClass_pair
    geo_chunk
    rw [h8]
    geo_step step_integer_valueOf
    geo_chunk
    rw [h9]
    geo_step step_integer_valueOf
    geo_chunk
    geo_step step_pair_init
    geo_chunk
    geo_step step_newClass_pair
    geo_chunk
    rw [h10]
    geo_step step_integer_valueOf
    geo_chunk
    rw [h11]
    geo_step step_integer_valueOf
    geo_chunk
    geo_step step_pair_init
    geo_chunk
    geo_step (step_anewarray hnn0')
    geo_chunk
    geo_step (step_arraylength ha0)
    geo_chunk
    rw [show (UInt32.ofNat (#[] : Array JvmVal).size).add (UInt32.ofNat 1) = UInt32.ofNat 1 from rfl]
    geo_step (step_arrays_copyOf hnn1 ha0)
    geo_chunk
    geo_step step_intrinsics_checkNotNullExpr
    geo_chunk
    geo_step (step_arraylength ha0_in_a1)
    geo_chunk
    rw [show UInt32.ofNat (#[] : Array JvmVal).size = UInt32.ofNat 0 from rfl]
    geo_step (step_aastore hnn0' ha1_self (by simp [copied1]))
    geo_chunk
    geo_step (step_arraylength ha1_in_h3)
    geo_chunk
    rw [show (UInt32.ofNat (#[pair0] : Array JvmVal).size).add (UInt32.ofNat 1) = UInt32.ofNat 2 from rfl]
    geo_step (step_arrays_copyOf hnn2 ha1_in_h3)
    geo_chunk
    geo_step step_intrinsics_checkNotNullExpr
    geo_chunk
    geo_step (step_arraylength ha1_in_a2)
    geo_chunk
    rw [show UInt32.ofNat (#[pair0] : Array JvmVal).size = UInt32.ofNat 1 from rfl]
    geo_step (step_aastore hnn1 ha2_self (by simp [copied2]))
    geo_chunk
    rw [h0, h2, h16, h17, h10, h11, h8, h9]
    geo_step (step_rayMarchLoop_call ha2_in_h5
      (by simpa [pair0, pair1, encodeCoordPairs] using
        decodeCoordArray_encodeCoordPairs #[(startCellX, startCellY), (endCellX, endCellY)]))
    geo_chunk
    geo_step step_intrinsics_checkNotNull
    geo_chunk
    geo_step (step_checkcast_objArray (get?_alloc_self h5 _))
    geo_chunk
    exact rfl
  case hget =>
    rw [get?_alloc_self h5]
    simp only [asI32_i32, asF64_f64]
    rw [rayMarchLoop_dx_dy_irrel (dx := 0.0) (dx' := endX - startX) (dy := 0.0) (dy' := endY - startY)]
    rfl

private theorem geoDcmpg_lt_iff (a b : Float) :
    ((geoDcmpg a b).toBitVec.slt 0#32) = decide (a < b) := by
  by_cases hlt : a < b
  · simp [geoDcmpg, hlt]
  · by_cases heq : a == b <;> simp [geoDcmpg, hlt, heq]

private theorem geoDcmpg_le_iff (a b : Float) :
    ((geoDcmpg a b).toBitVec.sle 0#32) = decide (a < b ∨ a == b) := by
  by_cases hlt : a < b
  · simp [geoDcmpg, hlt]
  · by_cases heq : a == b <;> simp [geoDcmpg, hlt, heq]

private theorem seg_from98 (k : Nat) (startX startY endX endY : Float)
    (startCellX startCellY endCellX endCellY stepX : Int32)
    (locs : Nat → JvmVal)
    (h18 : locs 18 = .f64 0.0)
    (h20 : locs 20 = .f64 (endX - startX))
    (h22 : locs 22 = .f64 (endY - startY))
    (h24 : locs 24 = .i32 stepX.toUInt32)
    (h0 : locs 0 = .f64 startX)
    (h2 : locs 2 = .f64 startY)
    (h8 : locs 8 = .i32 startCellX.toUInt32)
    (h9 : locs 9 = .i32 startCellY.toUInt32)
    (h10 : locs 10 = .i32 endCellX.toUInt32)
    (h11 : locs 11 = .i32 endCellY.toUInt32) :
    let dy := endY - startY
    let stepY : Int32 := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
    ∃ outAddr st',
      Jvm.runJvmResFast geomHooks (k + 160) f_Geometry_rayMarchSegmentCoords_prog 98
          (f_Geometry_rayMarchSegmentCoords_prog.drop 98)
          { pc := 98, stack := [], locals := locs, jvmHeap := {}, heap := () } =
        some (.heapRef outAddr, st') ∧
      st'.jvmHeap.get? outAddr = some (.objArray "java/lang/Object" (encodeCoordPairs
        (Geometry.rayMarchLoop
          (Geometry.absInt (endCellX - startCellX) + Geometry.absInt (endCellY - startCellY) + 2)
          startX startY (endX - startX) dy
          (Geometry.absFloat (endX - startX)) (Geometry.absFloat dy)
          stepX stepY endCellX endCellY startCellX startCellY
          #[(startCellX, startCellY), (endCellX, endCellY)]))) := by
  intro dy stepY
  by_cases hpos : (0.0 : Float) < dy
  · have hstep : stepY = 1 := by simp [stepY, hpos]
    rw [hstep]
    have hpos_dc : ((geoDcmpg 0.0 dy).toBitVec.slt 0#32) = true := by
      rw [geoDcmpg_lt_iff]; simp [hpos]
    let locs' := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
      12 (.f64 dy)) 14 (.f64 (endX - startX))) 16 (.i32 stepX.toUInt32)) 17 (.i32 (UInt32.ofNat 1))
    have hrun132 := seg_from132 (k + 28) startX startY endX endY startCellX startCellY endCellX endCellY stepX 1 locs'
      rfl rfl rfl rfl
      (by simp [locs', Jvm.setLocal, h0]) (by simp [locs', Jvm.setLocal, h2])
      (by simp [locs', Jvm.setLocal, h8]) (by simp [locs', Jvm.setLocal, h9])
      (by simp [locs', Jvm.setLocal, h10]) (by simp [locs', Jvm.setLocal, h11])
    rcases hrun132 with ⟨outAddr, st', hrun, hget⟩
    refine ⟨outAddr, st', ?_, hget⟩
    rw [← hrun]
    rw [show k + 160 = (k + 28 + 120) + 12 from by omega]
    geo_chunk
    rw [h18, h22]
    geo_step step_dcmpg
    geo_branch_step (branch_iflt_true hpos_dc)
    geo_chunk_n 8
    rw [h20, h22, h24]
    exact runJvmResFast_eq rfl rfl
  · by_cases hneg : dy < 0.0
    · have hstep : stepY = -1 := by simp [stepY, hpos, hneg]
      rw [hstep]
      have hpos_dc : ((geoDcmpg 0.0 dy).toBitVec.slt 0#32) = false := by
        rw [geoDcmpg_lt_iff]; simp [hpos]
      have hneg_dc : ((geoDcmpg dy 0.0).toBitVec.slt 0#32) = true := by
        rw [geoDcmpg_lt_iff]; simp [hneg]
      let locs' := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
        12 (.f64 dy)) 14 (.f64 (endX - startX))) 16 (.i32 stepX.toUInt32)) 17 (.i32 (UInt32.ofNat 4294967295))
      have hrun132 := seg_from132 (k + 23) startX startY endX endY startCellX startCellY endCellX endCellY stepX (-1) locs'
        rfl rfl rfl rfl
        (by simp [locs', Jvm.setLocal, h0]) (by simp [locs', Jvm.setLocal, h2])
        (by simp [locs', Jvm.setLocal, h8]) (by simp [locs', Jvm.setLocal, h9])
        (by simp [locs', Jvm.setLocal, h10]) (by simp [locs', Jvm.setLocal, h11])
      rcases hrun132 with ⟨outAddr, st', hrun, hget⟩
      refine ⟨outAddr, st', ?_, hget⟩
      rw [← hrun]
      rw [show k + 160 = (k + 23 + 120) + 17 from by omega]
      geo_chunk
      rw [h18, h22]
      geo_step step_dcmpg
      geo_branch_step (branch_iflt_false hpos_dc)
      geo_chunk
      rw [h18, h22]
      geo_step step_dcmpg
      geo_branch_step (branch_iflt_true hneg_dc)
      geo_chunk
      rw [h20, h22, h24]
      exact branch_goto_eq rfl
    · have hstep : stepY = 0 := by simp [stepY, hpos, hneg]
      rw [hstep]
      have hpos_dc : ((geoDcmpg 0.0 dy).toBitVec.slt 0#32) = false := by
        rw [geoDcmpg_lt_iff]; simp [hpos]
      have hneg_dc : ((geoDcmpg dy 0.0).toBitVec.slt 0#32) = false := by
        rw [geoDcmpg_lt_iff]; simp [hneg]
      let locs' := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
        12 (.f64 dy)) 14 (.f64 (endX - startX))) 16 (.i32 stepX.toUInt32)) 17 (.i32 (UInt32.ofNat 0))
      have hrun132 := seg_from132 (k + 23) startX startY endX endY startCellX startCellY endCellX endCellY stepX 0 locs'
        rfl rfl rfl rfl
        (by simp [locs', Jvm.setLocal, h0]) (by simp [locs', Jvm.setLocal, h2])
        (by simp [locs', Jvm.setLocal, h8]) (by simp [locs', Jvm.setLocal, h9])
        (by simp [locs', Jvm.setLocal, h10]) (by simp [locs', Jvm.setLocal, h11])
      rcases hrun132 with ⟨outAddr, st', hrun, hget⟩
      refine ⟨outAddr, st', ?_, hget⟩
      rw [← hrun]
      rw [show k + 160 = (k + 23 + 120) + 17 from by omega]
      geo_chunk
      rw [h18, h22]
      geo_step step_dcmpg
      geo_branch_step (branch_iflt_false hpos_dc)
      geo_chunk
      rw [h18, h22]
      geo_step step_dcmpg
      geo_branch_step (branch_iflt_false hneg_dc)
      geo_chunk
      rw [h20, h22, h24]
      exact branch_goto_eq rfl

private theorem seg_from54 (k : Nat) (startX startY endX endY : Float)
    (startCellX startCellY endCellX endCellY : Int32)
    (locs : Nat → JvmVal)
    (h0 : locs 0 = .f64 startX)
    (h2 : locs 2 = .f64 startY)
    (h4 : locs 4 = .f64 endX)
    (h6 : locs 6 = .f64 endY)
    (h8 : locs 8 = .i32 startCellX.toUInt32)
    (h9 : locs 9 = .i32 startCellY.toUInt32)
    (h10 : locs 10 = .i32 endCellX.toUInt32)
    (h11 : locs 11 = .i32 endCellY.toUInt32) :
    let dx := endX - startX
    let dy := endY - startY
    let stepX : Int32 := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
    let stepY : Int32 := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
    ∃ outAddr st',
      Jvm.runJvmResFast geomHooks (k + 200) f_Geometry_rayMarchSegmentCoords_prog 54
          (f_Geometry_rayMarchSegmentCoords_prog.drop 54)
          { pc := 54, stack := [], locals := locs, jvmHeap := {}, heap := () } =
        some (.heapRef outAddr, st') ∧
      st'.jvmHeap.get? outAddr = some (.objArray "java/lang/Object" (encodeCoordPairs
        (Geometry.rayMarchLoop
          (Geometry.absInt (endCellX - startCellX) + Geometry.absInt (endCellY - startCellY) + 2)
          startX startY dx dy (Geometry.absFloat dx) (Geometry.absFloat dy)
          stepX stepY endCellX endCellY startCellX startCellY
          #[(startCellX, startCellY), (endCellX, endCellY)]))) := by
  intro dx dy stepX stepY
  by_cases hpos : (0.0 : Float) < dx
  · have hstep : stepX = 1 := by simp [stepX, hpos]
    rw [hstep]
    have hpos_dc : ((geoDcmpg 0.0 dx).toBitVec.slt 0#32) = true := by
      rw [geoDcmpg_lt_iff]; simp [hpos]
    let locs0 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
      25 (.f64 (endX.sub startX))) 27 (.f64 (endY.sub startY))) 29 (.f64 0.0)
    let locs' := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs0
      18 (.f64 0.0)) 20 (.f64 (endX.sub startX))) 22 (.f64 (endY.sub startY))) 24 (.i32 (UInt32.ofNat 1))
    have hrun98 := seg_from98 (k + 18) startX startY endX endY startCellX startCellY endCellX endCellY 1 locs'
      rfl rfl rfl rfl
      (by simp [locs', locs0, Jvm.setLocal, h0]) (by simp [locs', locs0, Jvm.setLocal, h2])
      (by simp [locs', locs0, Jvm.setLocal, h8]) (by simp [locs', locs0, Jvm.setLocal, h9])
      (by simp [locs', locs0, Jvm.setLocal, h10]) (by simp [locs', locs0, Jvm.setLocal, h11])
    rcases hrun98 with ⟨outAddr, st', hrun, hget⟩
    refine ⟨outAddr, st', ?_, hget⟩
    rw [← hrun]
    rw [show k + 200 = (k + 18 + 160) + 22 from by omega]
    geo_chunk
    rw [h4, h0, h6, h2]
    simp only [asF64_f64]
    geo_step step_absFloat_closed0
    geo_chunk
    geo_step step_dcmpg
    rw [show endX.sub startX = dx from rfl]
    geo_branch_step (branch_iflt_true hpos_dc)
    geo_chunk_n 8
    exact runJvmResFast_eq rfl rfl
  · by_cases hneg : dx < 0.0
    · have hstep : stepX = -1 := by simp [stepX, hpos, hneg]
      rw [hstep]
      have hpos_dc : ((geoDcmpg 0.0 dx).toBitVec.slt 0#32) = false := by
        rw [geoDcmpg_lt_iff]; simp [hpos]
      have hneg_dc : ((geoDcmpg dx 0.0).toBitVec.slt 0#32) = true := by
        rw [geoDcmpg_lt_iff]; simp [hneg]
      let locs0 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
        25 (.f64 (endX.sub startX))) 27 (.f64 (endY.sub startY))) 29 (.f64 0.0)
      let locs' := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs0
        18 (.f64 0.0)) 20 (.f64 (endX.sub startX))) 22 (.f64 (endY.sub startY))) 24 (.i32 (UInt32.ofNat 4294967295))
      have hrun98 := seg_from98 (k + 13) startX startY endX endY startCellX startCellY endCellX endCellY (-1) locs'
        rfl rfl rfl rfl
        (by simp [locs', locs0, Jvm.setLocal, h0]) (by simp [locs', locs0, Jvm.setLocal, h2])
        (by simp [locs', locs0, Jvm.setLocal, h8]) (by simp [locs', locs0, Jvm.setLocal, h9])
        (by simp [locs', locs0, Jvm.setLocal, h10]) (by simp [locs', locs0, Jvm.setLocal, h11])
      rcases hrun98 with ⟨outAddr, st', hrun, hget⟩
      refine ⟨outAddr, st', ?_, hget⟩
      rw [← hrun]
      rw [show k + 200 = (k + 13 + 160) + 27 from by omega]
      geo_chunk
      rw [h4, h0, h6, h2]
      simp only [asF64_f64]
      geo_step step_absFloat_closed0
      geo_chunk
      geo_step step_dcmpg
      rw [show endX.sub startX = dx from rfl]
      geo_branch_step (branch_iflt_false hpos_dc)
      geo_chunk
      geo_step step_dcmpg
      rw [show endX.sub startX = dx from rfl]
      geo_branch_step (branch_iflt_true hneg_dc)
      geo_chunk
      exact branch_goto_eq rfl
    · have hstep : stepX = 0 := by simp [stepX, hpos, hneg]
      rw [hstep]
      have hpos_dc : ((geoDcmpg 0.0 dx).toBitVec.slt 0#32) = false := by
        rw [geoDcmpg_lt_iff]; simp [hpos]
      have hneg_dc : ((geoDcmpg dx 0.0).toBitVec.slt 0#32) = false := by
        rw [geoDcmpg_lt_iff]; simp [hneg]
      let locs0 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
        25 (.f64 (endX.sub startX))) 27 (.f64 (endY.sub startY))) 29 (.f64 0.0)
      let locs' := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs0
        18 (.f64 0.0)) 20 (.f64 (endX.sub startX))) 22 (.f64 (endY.sub startY))) 24 (.i32 (UInt32.ofNat 0))
      have hrun98 := seg_from98 (k + 13) startX startY endX endY startCellX startCellY endCellX endCellY 0 locs'
        rfl rfl rfl rfl
        (by simp [locs', locs0, Jvm.setLocal, h0]) (by simp [locs', locs0, Jvm.setLocal, h2])
        (by simp [locs', locs0, Jvm.setLocal, h8]) (by simp [locs', locs0, Jvm.setLocal, h9])
        (by simp [locs', locs0, Jvm.setLocal, h10]) (by simp [locs', locs0, Jvm.setLocal, h11])
      rcases hrun98 with ⟨outAddr, st', hrun, hget⟩
      refine ⟨outAddr, st', ?_, hget⟩
      rw [← hrun]
      rw [show k + 200 = (k + 13 + 160) + 27 from by omega]
      geo_chunk
      rw [h4, h0, h6, h2]
      simp only [asF64_f64]
      geo_step step_absFloat_closed0
      geo_chunk
      geo_step step_dcmpg
      rw [show endX.sub startX = dx from rfl]
      geo_branch_step (branch_iflt_false hpos_dc)
      geo_chunk
      geo_step step_dcmpg
      rw [show endX.sub startX = dx from rfl]
      geo_branch_step (branch_iflt_false hneg_dc)
      geo_chunk
      exact branch_goto_eq rfl

theorem rayMarchSegmentCoords_equiv (startX startY endX endY : Float)
    (startCellX startCellY endCellX endCellY : Int32) :
    ∃ outAddr st',
      Jvm.runJvmRes geomHooks 250 f_Geometry_rayMarchSegmentCoords_prog
          (initJvmState
            [ (0, .f64 startX), (2, .f64 startY), (4, .f64 endX), (6, .f64 endY),
              (8, .i32 startCellX.toUInt32), (9, .i32 startCellY.toUInt32),
              (10, .i32 endCellX.toUInt32), (11, .i32 endCellY.toUInt32) ]) =
        some (.heapRef outAddr, st') ∧
      st'.jvmHeap.get? outAddr = some (.objArray "java/lang/Object" (encodeCoordPairs
        (Geometry.rayMarchSegmentCoords startX startY endX endY startCellX startCellY endCellX endCellY))) := by
  dsimp [Geometry.rayMarchSegmentCoords]
  let st0 := initJvmState
    [ (0, .f64 startX), (2, .f64 startY), (4, .f64 endX), (6, .f64 endY),
      (8, .i32 startCellX.toUInt32), (9, .i32 startCellY.toUInt32),
      (10, .i32 endCellX.toUInt32), (11, .i32 endCellY.toUInt32) ]
  let locsInit := st0.locals
  let locsBase := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal
    (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locsInit
      12 (.f64 0.0)) 14 (.f64 0.0)) 16 (.i32 (UInt32.ofNat 0))) 17 (.i32 (UInt32.ofNat 0)))
      18 (.f64 0.0)) 20 (.f64 0.0)) 22 (.f64 0.0)) 24 (.i32 (UInt32.ofNat 0))
  by_cases hx : startCellX = endCellX
  · by_cases hy : startCellY = endCellY
    · have hcond : (startCellX == endCellX && startCellY == endCellY) = true := by
        simp [hx, hy]
      simp only [hcond, ↓reduceIte]
      have hx_u : startCellX.toUInt32 = endCellX.toUInt32 := congrArg Int32.toUInt32 hx
      have hy_u : startCellY.toUInt32 = endCellY.toUInt32 := congrArg Int32.toUInt32 hy
      have hlt0 : 0 < 2 ^ 31 := by decide
      have hlt1 : 1 < 2 ^ 31 := by decide
      have hnn0' : (UInt32.ofNat 0).toBitVec.slt 0#32 = false := ui32_slt_zero_of_lt 0 hlt0
      have hnn1 : (UInt32.ofNat 1).toBitVec.slt 0#32 = false := ui32_slt_zero_of_lt 1 hlt1
      let pair0 : JvmVal := .pair (.boxedInt startCellX.toUInt32) (.boxedInt startCellY.toUInt32)
      let h_empty : Jvm.JvmHeap Empty := {}
      let a0 := h_empty.alloc (.objArray "java/lang/Object" (Array.replicate (UInt32.ofNat 0).toNat .null))
      have ha0 : a0.2.get? a0.1 = some (.objArray "java/lang/Object" #[]) := by
        simpa [a0] using get?_alloc_self h_empty (.objArray "java/lang/Object" #[])
      let copied1 : Array JvmVal := Array.ofFn (n := (UInt32.ofNat 1).toNat)
        (fun i => if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val] else .null)
      let a1 := a0.2.alloc (.objArray "java/lang/Object" copied1)
      have ha0_in_a1 : a1.2.get? a0.1 = some (.objArray "java/lang/Object" #[]) :=
        get?_alloc_old a0.2 _ ha0
      have ha1_self : a1.2.get? a1.1 = some (.objArray "java/lang/Object" copied1) :=
        get?_alloc_self a0.2 _
      have ha1_lt : a1.1 < a1.2.objects.size := alloc_fst_lt a0.2 _
      let h3 := a1.2.set a1.1 (.objArray "java/lang/Object" (copied1.set (UInt32.ofNat 0).toNat pair0 (by simp [copied1])))
      have hpush1 : copied1.set (UInt32.ofNat 0).toNat pair0 (by simp [copied1]) = #[pair0] := by
        apply Array.ext
        · simp [copied1]
        · intro i _ hi₂; simp only [List.size_toArray, List.length_cons, List.length_nil] at hi₂
          simp [copied1, show i = 0 by omega]
      refine ⟨?outAddr, ?st', ?hrun, ?hget⟩
      case hrun =>
        apply Jvm.runJvmRes_of_runJvmResFast0 (hpc := rfl)
        change Jvm.runJvmResFast geomHooks 250 f_Geometry_rayMarchSegmentCoords_prog 0
          (f_Geometry_rayMarchSegmentCoords_prog.drop 0) st0 = _
        geo_chunk
        geo_branch_step (branch_if_icmpne_false hx_u)
        geo_chunk
        geo_branch_step (branch_if_icmpne_false hy_u)
        geo_step step_newClass_pair
        geo_chunk
        geo_step step_integer_valueOf
        geo_chunk
        geo_step step_integer_valueOf
        geo_step step_pair_init
        geo_chunk
        geo_step (step_anewarray hnn0')
        geo_chunk
        geo_step (step_arraylength ha0)
        geo_chunk
        rw [show (UInt32.ofNat (#[] : Array JvmVal).size).add (UInt32.ofNat 1) = UInt32.ofNat 1 from rfl]
        geo_step (step_arrays_copyOf hnn1 ha0)
        geo_chunk
        geo_step step_intrinsics_checkNotNullExpr
        geo_chunk
        geo_step (step_arraylength ha0_in_a1)
        geo_chunk
        rw [show UInt32.ofNat (#[] : Array JvmVal).size = UInt32.ofNat 0 from rfl]
        geo_step (step_aastore hnn0' ha1_self (by simp [copied1]))
        geo_chunk
        exact rfl
      case hget =>
        rw [get?_set_self a1.2 a1.1 _ ha1_lt, hpush1]
        simp [encodeCoordPairs, pair0]
    · have hcond : (startCellX == endCellX && startCellY == endCellY) = false := by
        simp [hx, hy]
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      have hx_u : startCellX.toUInt32 = endCellX.toUInt32 := congrArg Int32.toUInt32 hx
      have hy_u : startCellY.toUInt32 ≠ endCellY.toUInt32 := fun h => hy (congrArg UInt32.toInt32 h)
      have hrun54 := seg_from54 28 startX startY endX endY startCellX startCellY endCellX endCellY locsBase
        rfl rfl rfl rfl rfl rfl rfl rfl
      rcases hrun54 with ⟨outAddr, st', hrun, hget⟩
      refine ⟨outAddr, st', ?_, hget⟩
      apply Jvm.runJvmRes_of_runJvmResFast0 geomHooks _ _ _ _ rfl
      rw [← hrun]
      change Jvm.runJvmResFast geomHooks (28 + 200 + 22) f_Geometry_rayMarchSegmentCoords_prog 0
        (f_Geometry_rayMarchSegmentCoords_prog.drop 0) st0 = _
      geo_chunk
      geo_branch_step (branch_if_icmpne_false hx_u)
      geo_chunk
      geo_branch_step (branch_if_icmpne_true hy_u)
      exact runJvmResFast_eq rfl rfl
  · have hcond : (startCellX == endCellX && startCellY == endCellY) = false := by
      simp [hx]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hx_u : startCellX.toUInt32 ≠ endCellX.toUInt32 := fun h => hx (congrArg UInt32.toInt32 h)
    have hrun54 := seg_from54 31 startX startY endX endY startCellX startCellY endCellX endCellY locsBase
      rfl rfl rfl rfl rfl rfl rfl rfl
    rcases hrun54 with ⟨outAddr, st', hrun, hget⟩
    refine ⟨outAddr, st', ?_, hget⟩
    apply Jvm.runJvmRes_of_runJvmResFast0 geomHooks _ _ _ _ rfl
    rw [← hrun]
    change Jvm.runJvmResFast geomHooks (31 + 200 + 19) f_Geometry_rayMarchSegmentCoords_prog 0
      (f_Geometry_rayMarchSegmentCoords_prog.drop 0) st0 = _
    geo_chunk
    geo_branch_step (branch_if_icmpne_true hx_u)
    exact runJvmResFast_eq rfl rfl

end RayMarchSegmentCoords

section RayMarchLoop

private theorem float_le_iff_lt_or_beq (a b : Float) : (a ≤ b) ↔ (a < b ∨ (a == b) = true) := by
  have : ∀ (c : Option Ordering),
      (decide (Option.any (fun x => x.isLE) c = true) = true) ↔
        (decide ((c == some Ordering.lt) = true) = true ∨ (c == some Ordering.eq) = true) := by
    rintro (_ | o)
    · simp
    · cases o <;> simp [Ordering.isLE]
  exact this (a.toModel.unpack.compare b.toModel.unpack)

private theorem geoDcmpg_fle_iff (a b : Float) :
    ((geoDcmpg a b).toBitVec.sle 0#32) = decide (a ≤ b) := by
  rw [geoDcmpg_le_iff, decide_eq_decide]
  exact (float_le_iff_lt_or_beq a b).symm

private structure LoopLocals (locals : Nat → JvmVal) (fuel : UInt32) (startX startY absDx absDy : Float)
    (stepX stepY endX endY curX curY : Int32) (accAddr : Nat) : Prop where
  h0 : locals 0 = .i32 fuel
  h1 : locals 1 = .f64 startX
  h3 : locals 3 = .f64 startY
  h5 : locals 5 = .f64 absDx
  h7 : locals 7 = .f64 absDy
  h9 : locals 9 = .i32 stepX.toUInt32
  h10 : locals 10 = .i32 stepY.toUInt32
  h11 : locals 11 = .i32 endX.toUInt32
  h12 : locals 12 = .i32 endY.toUInt32
  h13 : locals 13 = .i32 curX.toUInt32
  h14 : locals 14 = .i32 curY.toUInt32
  h15 : locals 15 = .heapRef accAddr

private theorem int32_pos_slt_iff (a : Int32) :
    ((0 : UInt32).toBitVec.slt a.toUInt32.toBitVec = true) ↔ ((0 : Int32) < a) :=
  Iff.rfl

private theorem array_len_nneg {m : Nat} (hm : m < 2 ^ 31) :
    ((UInt32.ofNat m).toBitVec.slt 0#32) = false := by
  have h1 : (UInt32.ofNat m).toBitVec = BitVec.ofNat 32 m := rfl
  rw [h1, BitVec.slt]
  have htoInt : (BitVec.ofNat 32 m).toInt = (m : Int) := by
    rw [BitVec.toInt_ofNat', Int.bmod]
    split <;> omega
  rw [htoInt]
  simp [BitVec.toInt_zero]

private theorem array_len_plus1_nneg {m : Nat} (hm : m + 1 < 2 ^ 31) :
    (((UInt32.ofNat m).add (UInt32.ofNat 1)).toBitVec.slt 0#32) = false := by
  have h1 : ((UInt32.ofNat m).add (UInt32.ofNat 1)).toBitVec = BitVec.ofNat 32 (m + 1) := by
    change (UInt32.ofNat m + UInt32.ofNat 1).toBitVec = _
    rw [UInt32.toBitVec_add]
    change BitVec.ofNat 32 m + BitVec.ofNat 32 1 = BitVec.ofNat 32 (m + 1)
    rw [BitVec.ofNat_add]
  rw [h1, BitVec.slt]
  have htoInt : (BitVec.ofNat 32 (m + 1)).toInt = ((m + 1 : Nat) : Int) := by
    rw [BitVec.toInt_ofNat', Int.bmod]
    split <;> omega
  rw [htoInt]
  simp [BitVec.toInt_zero]
  omega

private theorem encodeCoordPairs_size (acc : Array (Int32 × Int32)) :
    (encodeCoordPairs acc).size = acc.size := by
  simp [encodeCoordPairs]

private theorem array_copy_set_eq_push (src : Array JvmVal) (x : JvmVal)
    (hlen : src.size + 1 < 2 ^ 31) :
    let newLen := (UInt32.ofNat src.size).add (UInt32.ofNat 1)
    let copied : Array JvmVal := Array.ofFn (n := newLen.toNat)
      (fun i => if h : i.val < src.size then src[i.val] else .null)
    copied.set (UInt32.ofNat src.size).toNat x (by
      have hnew : newLen.toNat = src.size + 1 := by
        change ((UInt32.ofNat src.size + UInt32.ofNat 1).toNat) = src.size + 1
        rw [UInt32.toNat_add]
        change (src.size % 2 ^ 32 + 1 % 2 ^ 32) % 2 ^ 32 = src.size + 1
        omega
      have hold : (UInt32.ofNat src.size).toNat = src.size := by
        change src.size % 2 ^ 32 = src.size
        omega
      simp [copied, hnew, hold]) =
    src.push x := by
  intro newLen copied
  have hnew : newLen.toNat = src.size + 1 := by
    change ((UInt32.ofNat src.size + UInt32.ofNat 1).toNat) = src.size + 1
    rw [UInt32.toNat_add]
    change (src.size % 2 ^ 32 + 1 % 2 ^ 32) % 2 ^ 32 = src.size + 1
    omega
  have hold : (UInt32.ofNat src.size).toNat = src.size := by
    change src.size % 2 ^ 32 = src.size
    omega
  apply Array.ext
  · simp [copied, hnew]
  · intro i hi1 hi2
    simp only [Array.size_set, Array.size_push] at hi1 hi2
    rw [Array.getElem_set]
    split
    · next heq =>
      have : i = src.size := by omega
      subst this
      simp [Array.getElem_push]
    · next heq =>
      have hlt : i < src.size := by omega
      simp [copied, hlt, Array.getElem_push]

private theorem loop_from369
    {k accAddr : Nat} {fuel : UInt32} {startX startY absDx absDy : Float}
    {stepX stepY endX endY curX curY nextX nextY : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (h16 : locals 16 = .i32 nextX.toUInt32)
    (h17 : locals 17 = .i32 nextY.toUInt32)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31) :
    ∃ (locals' : Nat → JvmVal) (jh' : Jvm.JvmHeap Empty) (addr' : Nat) (cls' : String),
      (Jvm.runJvmResFast geomHooks (k + 79) f_Geometry_rayMarchLoop___redArg_prog 369
        (f_Geometry_rayMarchLoop___redArg_prog.drop 369)
        { pc := 369, stack := [], locals := locals, jvmHeap := jh, heap := () } =
      Jvm.runJvmResFast geomHooks k f_Geometry_rayMarchLoop___redArg_prog 0
        f_Geometry_rayMarchLoop___redArg_prog
        { pc := 0, stack := [], locals := locals', jvmHeap := jh', heap := () }) ∧
      LoopLocals locals' (fuel - 1) startX startY absDx absDy stepX stepY endX endY nextX nextY addr' ∧
      jh'.get? addr' = some (Jvm.HeapObj.objArray cls' (encodeCoordPairs (acc.push (nextX, nextY)))) := by
  have hlen : (encodeCoordPairs acc).size + 1 < 2 ^ 31 := by
    rw [encodeCoordPairs_size]; exact hsz
  have hnneg : (((UInt32.ofNat (encodeCoordPairs acc).size).add (UInt32.ofNat 1)).toBitVec.slt 0#32) = false :=
    array_len_plus1_nneg hlen
  have hidx_nneg : ((UInt32.ofNat (encodeCoordPairs acc).size).toBitVec.slt 0#32) = false :=
    array_len_nneg (by omega)
  let pairVal : JvmVal := .pair (.boxedInt nextX.toUInt32) (.boxedInt nextY.toUInt32)
  let newLen := (UInt32.ofNat (encodeCoordPairs acc).size).add (UInt32.ofNat 1)
  let copied : Array JvmVal := Array.ofFn (n := newLen.toNat)
    (fun i => if h : i.val < (encodeCoordPairs acc).size then (encodeCoordPairs acc)[i.val] else .null)
  let a' := jh.alloc (.objArray cls copied)
  have ha_old : a'.2.get? accAddr = some (.objArray cls (encodeCoordPairs acc)) :=
    get?_alloc_old jh _ hheap
  have ha'_self : a'.2.get? a'.1 = some (.objArray cls copied) :=
    get?_alloc_self jh _
  have ha'_lt : a'.1 < a'.2.objects.size := alloc_fst_lt jh _
  have hidx_lt : (UInt32.ofNat (encodeCoordPairs acc).size).toNat < copied.size := by
    have hnew : newLen.toNat = (encodeCoordPairs acc).size + 1 := by
      change ((UInt32.ofNat (encodeCoordPairs acc).size + UInt32.ofNat 1).toNat) = _
      rw [UInt32.toNat_add]
      change ((encodeCoordPairs acc).size % 2 ^ 32 + 1 % 2 ^ 32) % 2 ^ 32 = _
      omega
    have hold : (UInt32.ofNat (encodeCoordPairs acc).size).toNat = (encodeCoordPairs acc).size := by
      change (encodeCoordPairs acc).size % 2 ^ 32 = _
      omega
    simp [copied, hnew, hold]
  let jh' := a'.2.set a'.1 (.objArray cls (copied.set (UInt32.ofNat (encodeCoordPairs acc).size).toNat pairVal hidx_lt))
  have hpush : copied.set (UInt32.ofNat (encodeCoordPairs acc).size).toNat pairVal hidx_lt =
      encodeCoordPairs (acc.push (nextX, nextY)) := by
    rw [array_copy_set_eq_push (encodeCoordPairs acc) pairVal hlen]
    simp [pairVal, encodeCoordPairs, Array.map_push]
  have ha'_in_jh' : jh'.get? a'.1 = some (.objArray cls (encodeCoordPairs (acc.push (nextX, nextY)))) := by
    rw [← hpush]
    exact get?_set_self a'.2 a'.1 _ ha'_lt
  refine ⟨?locals', jh', a'.1, cls, ?heq, ?hl', ha'_in_jh'⟩
  case heq =>
    -- 369..371
    geo_chunk
    rw [hl.h0]
    -- 372: kotlin/UInt.constructor-impl
    geo_step step_uint_ctor
    -- 373..375
    geo_chunk
    rw [hl.h15]
    -- 376: Intrinsics.checkNotNull
    geo_step step_intrinsics_checkNotNull
    -- 377
    geo_chunk
    rw [hl.h15]
    -- 378: checkcast [Ljava/lang/Object;
    geo_step (step_checkcast_objArray hheap)
    -- 379
    geo_chunk
    rw [hl.h15]
    -- 380: checkcast [Ljava/lang/Object;
    geo_step (step_checkcast_objArray hheap)
    -- 381: arraylength
    geo_step (step_arraylength hheap)
    -- 382..383
    geo_chunk
    -- 384: Arrays.copyOf
    geo_step (step_arrays_copyOf hnneg hheap)
    -- 385..386
    geo_chunk
    -- 387: checkNotNullExpressionValue
    geo_step step_intrinsics_checkNotNullExpr
    -- 388..394
    geo_chunk
    rw [hl.h15]
    -- 395: checkcast
    geo_step (step_checkcast_objArray ha_old)
    -- 396: arraylength
    geo_step (step_arraylength ha_old)
    -- 397: newClass kotlin/Pair
    geo_step step_newClass_pair
    -- 398..399
    geo_chunk
    rw [h16]
    -- 400: Integer.valueOf
    geo_step step_integer_valueOf
    -- 401
    geo_chunk
    rw [h17]
    -- 402: Integer.valueOf
    geo_step step_integer_valueOf
    -- 403: Pair.<init>
    geo_step step_pair_init
    -- 404: aastore
    geo_step (step_aastore hidx_nneg ha'_self hidx_lt)
    -- 405..446
    geo_chunk
    -- 447: goto 0
    geo_branch_step (branch_goto_eq rfl)
    apply runJvmResFast_eq rfl
    congr 1
    rfl
  case hl' =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only <;>
      simp [Jvm.setLocal, ui32_sub_eq, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, h16, h17] <;>
      rfl

private def LoopResultOk (res : Option (JvmVal × JvmState)) (expected : Array (Int32 × Int32)) : Prop :=
  ∃ (st' : JvmState) (resAddr : Nat) (resCls : String),
    res = some (.heapRef resAddr, st') ∧
    st'.jvmHeap.get? resAddr = some (Jvm.HeapObj.objArray resCls (encodeCoordPairs expected))

private abbrev LoopRecHyp (fuel : UInt32) (startX startY dx dy absDx absDy : Float)
    (stepX stepY endX endY : Int32) (acc : Array (Int32 × Int32)) : Prop :=
  ∀ (k0 : Nat) (nextX nextY : Int32) (locals' : Nat → JvmVal) (jh' : Jvm.JvmHeap Empty)
    (addr' : Nat) (cls' : String),
    LoopLocals locals' (fuel - 1) startX startY absDx absDy stepX stepY endX endY nextX nextY addr' →
    jh'.get? addr' = some (Jvm.HeapObj.objArray cls' (encodeCoordPairs (acc.push (nextX, nextY)))) →
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k0 + (fuel - 1).toNat * 250 + 120) f_Geometry_rayMarchLoop___redArg_prog 0
        f_Geometry_rayMarchLoop___redArg_prog
        { pc := 0, stack := [], locals := locals', jvmHeap := jh', heap := () })
      (Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY
        (acc.push (nextX, nextY)))

private theorem loop_from352
    {k accAddr : Nat} {fuel : UInt32} {startX startY dx dy absDx absDy crossX crossY : Float}
    {stepX stepY endX endY curX curY nextX : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (h18 : locals 18 = .f64 crossY)
    (h20 : locals 20 = .f64 crossX)
    (h22 : locals 22 = .i32 nextX.toUInt32)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31)
    (hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + 91 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 352
        (f_Geometry_rayMarchLoop___redArg_prog.drop 352)
        { pc := 352, stack := [], locals := locals, jvmHeap := jh, heap := () })
      (let nextY := if crossY ≤ crossX then curY + stepY else curY
       Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY
         (acc.push (nextX, nextY))) := by
  dsimp only
  by_cases hle : crossY ≤ crossX
  · simp only [hle, ↓reduceIte]
    have hle_dc : ((geoDcmpg crossY crossX).toBitVec.sle 0#32) = true := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_true hle
    have hrun : ∃ (locals369 : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 91 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 352
          (f_Geometry_rayMarchLoop___redArg_prog.drop 352)
          { pc := 352, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks ((k + ((fuel - 1).toNat * 250 + 120)) + 79)
          f_Geometry_rayMarchLoop___redArg_prog 369
          (f_Geometry_rayMarchLoop___redArg_prog.drop 369)
          { pc := 369, stack := [], locals := locals369, jvmHeap := jh, heap := () } ∧
        LoopLocals locals369 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
        (locals369 16 = .i32 nextX.toUInt32 ∧
         locals369 17 = .i32 (curY + stepY).toUInt32) := by
      constructor
      apply And.intro
      · rw [show k + 91 + ((fuel - 1).toNat * 250 + 120) = ((k + ((fuel - 1).toNat * 250 + 120)) + 79) + 12 by omega]
        -- 352..353
        geo_chunk
        rw [h18, h20]
        -- 354: dcmpg
        geo_step step_dcmpg
        -- 355: ifle 361
        geo_branch_step (branch_ifle_true hle_dc)
        -- 361..368: 8 steps falling through to 369
        geo_chunk_n 8
        rw [hl.h14, hl.h10]
        exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ⟨?_, ?_⟩⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
        · simp [Jvm.setLocal, h22]
        · simp only [Jvm.setLocal]
          rw [asI32_i32, asI32_i32, ui32_add_eq, int32_toUInt32_add]
          simp
    rcases hrun with ⟨loc, heq, hl', h16, h17⟩
    rw [heq]
    rcases loop_from369 hl' h16 h17 hheap hsz with ⟨locals', jh', addr', cls', htail, hl'', hheap'⟩
    rw [htail]
    exact hrec k nextX (curY + stepY) locals' jh' addr' cls' hl'' hheap'
  · simp only [hle, ↓reduceIte]
    have hle_dc : ((geoDcmpg crossY crossX).toBitVec.sle 0#32) = false := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_false hle
    have hrun : ∃ (locals369 : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 91 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 352
          (f_Geometry_rayMarchLoop___redArg_prog.drop 352)
          { pc := 352, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks ((k + 3 + ((fuel - 1).toNat * 250 + 120)) + 79)
          f_Geometry_rayMarchLoop___redArg_prog 369
          (f_Geometry_rayMarchLoop___redArg_prog.drop 369)
          { pc := 369, stack := [], locals := locals369, jvmHeap := jh, heap := () } ∧
        LoopLocals locals369 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
        (locals369 16 = .i32 nextX.toUInt32 ∧
         locals369 17 = .i32 curY.toUInt32) := by
      constructor
      apply And.intro
      · rw [show k + 91 + ((fuel - 1).toNat * 250 + 120) = ((k + 3 + ((fuel - 1).toNat * 250 + 120)) + 79) + 9 by omega]
        -- 352..353
        geo_chunk
        rw [h18, h20]
        -- 354: dcmpg
        geo_step step_dcmpg
        -- 355: ifle 361 (false)
        geo_branch_step (branch_ifle_false hle_dc)
        -- 356..359
        geo_chunk
        -- 360: goto 369
        rw [branch_goto_eq rfl]
        try exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ⟨?_, ?_⟩⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
        · simp [Jvm.setLocal, h22]
        · simp [Jvm.setLocal, hl.h14]
    rcases hrun with ⟨loc, heq, hl', h16, h17⟩
    rw [heq]
    rcases loop_from369 hl' h16 h17 hheap hsz with ⟨locals', jh', addr', cls', htail, hl'', hheap'⟩
    rw [htail]
    exact hrec (k + 3) nextX curY locals' jh' addr' cls' hl'' hheap'

private theorem loop_from324
    {k accAddr : Nat} {fuel : UInt32} {startX startY dx dy absDx absDy limitCross crossY crossX minCross : Float}
    {stepX stepY endX endY curX curY : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (h23 : locals 23 = .f64 limitCross)
    (h25 : locals 25 = .f64 crossY)
    (h27 : locals 27 = .f64 crossX)
    (h29 : locals 29 = .f64 minCross)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31)
    (hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + 110 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 324
        (f_Geometry_rayMarchLoop___redArg_prog.drop 324)
        { pc := 324, stack := [], locals := locals, jvmHeap := jh, heap := () })
      (if minCross ≥ limitCross then acc
       else
         let nextX := if crossX ≤ crossY then curX + stepX else curX
         let nextY := if crossY ≤ crossX then curY + stepY else curY
         Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY
           (acc.push (nextX, nextY))) := by
  by_cases hlim : minCross ≥ limitCross
  · simp only [hlim, ↓reduceIte]
    have hlim_dc : ((geoDcmpg limitCross minCross).toBitVec.sle 0#32) = true := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_true hlim
    have hrun : Jvm.runJvmResFast geomHooks (k + 110 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 324
        (f_Geometry_rayMarchLoop___redArg_prog.drop 324)
        { pc := 324, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        some (.heapRef accAddr, { pc := 351, stack := [.heapRef accAddr], locals := locals, jvmHeap := jh, heap := () }) := by
      rw [show k + 110 + ((fuel - 1).toNat * 250 + 120) =
        (k + 104 + ((fuel - 1).toNat * 250 + 120)) + 6 by omega]
      -- 324..325
      geo_chunk
      rw [h23, h29]
      -- 326: dcmpg
      geo_step step_dcmpg
      -- 327: ifle 350
      geo_branch_step (branch_ifle_true hlim_dc)
      -- 350..351: aload 15, areturn
      geo_chunk
      rw [hl.h15]
    exact ⟨_, accAddr, cls, hrun, hheap⟩
  · simp only [hlim, ↓reduceIte]
    have hlim_dc : ((geoDcmpg limitCross minCross).toBitVec.sle 0#32) = false := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_false hlim
    by_cases hxy : crossX ≤ crossY
    · simp only [hxy, ↓reduceIte]
      have hxy_dc : ((geoDcmpg crossX crossY).toBitVec.sle 0#32) = true := by
        rw [geoDcmpg_fle_iff]; exact decide_eq_true hxy
      have hrun : ∃ (locals352 : Nat → JvmVal),
          Jvm.runJvmResFast geomHooks (k + 110 + ((fuel - 1).toNat * 250 + 120))
            f_Geometry_rayMarchLoop___redArg_prog 324
            (f_Geometry_rayMarchLoop___redArg_prog.drop 324)
            { pc := 324, stack := [], locals := locals, jvmHeap := jh, heap := () } =
          Jvm.runJvmResFast geomHooks (k + 91 + ((fuel - 1).toNat * 250 + 120))
            f_Geometry_rayMarchLoop___redArg_prog 352
            (f_Geometry_rayMarchLoop___redArg_prog.drop 352)
            { pc := 352, stack := [], locals := locals352, jvmHeap := jh, heap := () } ∧
          LoopLocals locals352 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
          (locals352 18 = .f64 crossY ∧
           locals352 20 = .f64 crossX ∧
           locals352 22 = .i32 (curX + stepX).toUInt32) := by
        constructor
        apply And.intro
        · rw [show k + 110 + ((fuel - 1).toNat * 250 + 120) =
            (k + 91 + ((fuel - 1).toNat * 250 + 120)) + 19 by omega]
          geo_chunk
          rw [h23, h29]
          geo_step step_dcmpg
          geo_branch_step (branch_ifle_false hlim_dc)
          geo_chunk
          rw [h27, h25]
          geo_step step_dcmpg
          geo_branch_step (branch_ifle_true hxy_dc)
          geo_chunk
          rw [hl.h13, hl.h9, h25, h27]
          rw [branch_goto_eq rfl]
          try exact runJvmResFast_eq rfl rfl
        · refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
          · simp [Jvm.setLocal]
          · simp [Jvm.setLocal]
          · simp only [Jvm.setLocal]
            rw [asI32_i32, asI32_i32, ui32_add_eq, int32_toUInt32_add]
            simp
      rcases hrun with ⟨loc, heq, hl', h18', h20', h22'⟩
      rw [heq]
      exact loop_from352 hl' h18' h20' h22' hheap hsz hrec
    · simp only [hxy, ↓reduceIte]
      have hxy_dc : ((geoDcmpg crossX crossY).toBitVec.sle 0#32) = false := by
        rw [geoDcmpg_fle_iff]; exact decide_eq_false hxy
      have hrun : ∃ (locals352 : Nat → JvmVal),
          Jvm.runJvmResFast geomHooks (k + 110 + ((fuel - 1).toNat * 250 + 120))
            f_Geometry_rayMarchLoop___redArg_prog 324
            (f_Geometry_rayMarchLoop___redArg_prog.drop 324)
            { pc := 324, stack := [], locals := locals, jvmHeap := jh, heap := () } =
          Jvm.runJvmResFast geomHooks ((k + 4) + 91 + ((fuel - 1).toNat * 250 + 120))
            f_Geometry_rayMarchLoop___redArg_prog 352
            (f_Geometry_rayMarchLoop___redArg_prog.drop 352)
            { pc := 352, stack := [], locals := locals352, jvmHeap := jh, heap := () } ∧
          LoopLocals locals352 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
          (locals352 18 = .f64 crossY ∧
           locals352 20 = .f64 crossX ∧
           locals352 22 = .i32 curX.toUInt32) := by
        constructor
        apply And.intro
        · rw [show k + 110 + ((fuel - 1).toNat * 250 + 120) =
            ((k + 4) + 91 + ((fuel - 1).toNat * 250 + 120)) + 15 by omega]
          geo_chunk
          rw [h23, h29]
          geo_step step_dcmpg
          geo_branch_step (branch_ifle_false hlim_dc)
          geo_chunk
          rw [h27, h25]
          geo_step step_dcmpg
          geo_branch_step (branch_ifle_false hxy_dc)
          geo_chunk
          rw [h25, h27, hl.h13]
          rw [branch_goto_eq rfl]
          try exact runJvmResFast_eq rfl rfl
        · refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
          · simp [Jvm.setLocal]
          · simp [Jvm.setLocal]
          · simp [Jvm.setLocal]
      rcases hrun with ⟨loc, heq, hl', h18', h20', h22'⟩
      rw [heq]
      exact loop_from352 hl' h18' h20' h22' hheap hsz hrec

private theorem loop_from132
    {k accAddr : Nat} {fuel : UInt32} {startX startY dx dy absDx absDy xb : Float}
    {stepX stepY endX endY curX curY : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (h31 : locals 31 = .f64 xb)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31)
    (hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + 94 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 132
        (f_Geometry_rayMarchLoop___redArg_prog.drop 132)
        { pc := 132, stack := [], locals := locals, jvmHeap := jh, heap := () })
      (let remX := Geometry.absFloat (xb - startX)
       if remX ≥ absDx then acc
       else
         let nextX := curX + stepX
         Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX curY
           (acc.push (nextX, curY))) := by
  dsimp only
  by_cases hrem : Geometry.absFloat (xb - startX) ≥ absDx
  · simp only [hrem, ↓reduceIte]
    have hrem_dc : ((geoDcmpg absDx (Geometry.absFloat (xb - startX))).toBitVec.sle 0#32) = true := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_true hrem
    have hrun : Jvm.runJvmResFast geomHooks (k + 94 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 132
        (f_Geometry_rayMarchLoop___redArg_prog.drop 132)
        { pc := 132, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        some (.heapRef accAddr,
          { pc := 227, stack := [.heapRef accAddr],
            locals := Jvm.setLocal locals 39 (.f64 (Geometry.absFloat (xb.sub startX))),
            jvmHeap := jh, heap := () }) := by
      rw [show k + 94 + ((fuel - 1).toNat * 250 + 120) =
        (k + 83 + ((fuel - 1).toNat * 250 + 120)) + 11 by omega]
      -- 132..134
      geo_chunk
      rw [h31, hl.h1]
      -- 135: absFloat
      geo_step step_absFloat
      -- 136..138
      geo_chunk
      rw [hl.h5, show xb.sub startX = xb - startX from rfl]
      -- 139: dcmpg
      geo_step step_dcmpg
      -- 140: ifle 226
      geo_branch_step (branch_ifle_true hrem_dc)
      -- 226..227: aload 15, areturn
      geo_chunk
      rw [hl.h15]
      rfl
    exact ⟨_, accAddr, cls, hrun, hheap⟩
  · simp only [hrem, ↓reduceIte]
    have hrem_dc : ((geoDcmpg absDx (Geometry.absFloat (xb - startX))).toBitVec.sle 0#32) = false := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_false hrem
    have hlen : (encodeCoordPairs acc).size + 1 < 2 ^ 31 := by
      rw [encodeCoordPairs_size]; exact hsz
    have hnneg : (((UInt32.ofNat (encodeCoordPairs acc).size).add (UInt32.ofNat 1)).toBitVec.slt 0#32) = false :=
      array_len_plus1_nneg hlen
    have hidx_nneg : ((UInt32.ofNat (encodeCoordPairs acc).size).toBitVec.slt 0#32) = false :=
      array_len_nneg (by omega)
    let nextX := curX + stepX
    let pairVal : JvmVal := .pair (.boxedInt nextX.toUInt32) (.boxedInt curY.toUInt32)
    let newLen := (UInt32.ofNat (encodeCoordPairs acc).size).add (UInt32.ofNat 1)
    let copied : Array JvmVal := Array.ofFn (n := newLen.toNat)
      (fun i => if h : i.val < (encodeCoordPairs acc).size then (encodeCoordPairs acc)[i.val] else .null)
    let a' := jh.alloc (.objArray cls copied)
    have ha_old : a'.2.get? accAddr = some (.objArray cls (encodeCoordPairs acc)) :=
      get?_alloc_old jh _ hheap
    have ha'_self : a'.2.get? a'.1 = some (.objArray cls copied) :=
      get?_alloc_self jh _
    have ha'_lt : a'.1 < a'.2.objects.size := alloc_fst_lt jh _
    have hidx_lt : (UInt32.ofNat (encodeCoordPairs acc).size).toNat < copied.size := by
      have hnew : newLen.toNat = (encodeCoordPairs acc).size + 1 := by
        change ((UInt32.ofNat (encodeCoordPairs acc).size + UInt32.ofNat 1).toNat) = _
        rw [UInt32.toNat_add]
        change ((encodeCoordPairs acc).size % 2 ^ 32 + 1 % 2 ^ 32) % 2 ^ 32 = _
        omega
      have hold : (UInt32.ofNat (encodeCoordPairs acc).size).toNat = (encodeCoordPairs acc).size := by
        change (encodeCoordPairs acc).size % 2 ^ 32 = _
        omega
      simp [copied, hnew, hold]
    let jh' := a'.2.set a'.1 (.objArray cls (copied.set (UInt32.ofNat (encodeCoordPairs acc).size).toNat pairVal hidx_lt))
    have hpush : copied.set (UInt32.ofNat (encodeCoordPairs acc).size).toNat pairVal hidx_lt =
        encodeCoordPairs (acc.push (nextX, curY)) := by
      rw [array_copy_set_eq_push (encodeCoordPairs acc) pairVal hlen]
      simp [pairVal, encodeCoordPairs, Array.map_push]
    have ha'_in_jh' : jh'.get? a'.1 = some (.objArray cls (encodeCoordPairs (acc.push (nextX, curY)))) := by
      rw [← hpush]
      exact get?_set_self a'.2 a'.1 _ ha'_lt
    have hstep : ∃ (locals' : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 94 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 132
          (f_Geometry_rayMarchLoop___redArg_prog.drop 132)
          { pc := 132, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks (k + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 0
          f_Geometry_rayMarchLoop___redArg_prog
          { pc := 0, stack := [], locals := locals', jvmHeap := jh', heap := () } ∧
        LoopLocals locals' (fuel - 1) startX startY absDx absDy stepX stepY endX endY nextX curY a'.1 := by
      constructor
      apply And.intro
      · rw [show k + 94 + ((fuel - 1).toNat * 250 + 120) = (k + ((fuel - 1).toNat * 250 + 120)) + 94 by omega]
        geo_chunk
        rw [h31, hl.h1]
        geo_step step_absFloat
        geo_chunk
        rw [hl.h5, show xb.sub startX = xb - startX from rfl]
        geo_step step_dcmpg
        geo_branch_step (branch_ifle_false hrem_dc)
        geo_chunk
        rw [hl.h13, hl.h9, hl.h0, asI32_i32, asI32_i32, ui32_add_eq, int32_toUInt32_add]
        geo_step step_uint_ctor
        geo_chunk
        rw [hl.h15]
        geo_step step_intrinsics_checkNotNull
        geo_chunk
        rw [hl.h15]
        geo_step (step_checkcast_objArray hheap)
        geo_chunk
        rw [hl.h15]
        geo_step (step_checkcast_objArray hheap)
        geo_step (step_arraylength hheap)
        geo_chunk
        geo_step (step_arrays_copyOf hnneg hheap)
        geo_chunk
        geo_step step_intrinsics_checkNotNullExpr
        geo_chunk
        rw [hl.h15]
        geo_step (step_checkcast_objArray ha_old)
        geo_step (step_arraylength ha_old)
        geo_step step_newClass_pair
        geo_chunk
        geo_step step_integer_valueOf
        geo_chunk
        rw [hl.h14]
        geo_step step_integer_valueOf
        geo_step step_pair_init
        geo_step (step_aastore hidx_nneg ha'_self hidx_lt)
        geo_chunk
        geo_branch_step (branch_goto_eq rfl)
        exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          dsimp only <;>
          simp [Jvm.setLocal, ui32_sub_eq, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h14] <;>
          rfl
    rcases hstep with ⟨loc', heq, hl'⟩
    rw [heq]
    exact hrec k nextX curY loc' jh' a'.1 cls hl' ha'_in_jh'

private theorem loop_from228
    {k accAddr : Nat} {fuel : UInt32} {startX startY dx dy absDx absDy yb : Float}
    {stepX stepY endX endY curX curY : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (h34 : locals 34 = .f64 yb)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31)
    (hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + 94 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 228
        (f_Geometry_rayMarchLoop___redArg_prog.drop 228)
        { pc := 228, stack := [], locals := locals, jvmHeap := jh, heap := () })
      (let remY := Geometry.absFloat (yb - startY)
       if remY ≥ absDy then acc
       else
         let nextY := curY + stepY
         Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY curX nextY
           (acc.push (curX, nextY))) := by
  dsimp only
  by_cases hrem : Geometry.absFloat (yb - startY) ≥ absDy
  · simp only [hrem, ↓reduceIte]
    have hrem_dc : ((geoDcmpg absDy (Geometry.absFloat (yb - startY))).toBitVec.sle 0#32) = true := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_true hrem
    have hrun : Jvm.runJvmResFast geomHooks (k + 94 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 228
        (f_Geometry_rayMarchLoop___redArg_prog.drop 228)
        { pc := 228, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        some (.heapRef accAddr,
          { pc := 323, stack := [.heapRef accAddr],
            locals := Jvm.setLocal locals 39 (.f64 (Geometry.absFloat (yb.sub startY))),
            jvmHeap := jh, heap := () }) := by
      rw [show k + 94 + ((fuel - 1).toNat * 250 + 120) =
        (k + 83 + ((fuel - 1).toNat * 250 + 120)) + 11 by omega]
      geo_chunk
      rw [h34, hl.h3]
      geo_step step_absFloat
      geo_chunk
      rw [hl.h7, show yb.sub startY = yb - startY from rfl]
      geo_step step_dcmpg
      geo_branch_step (branch_ifle_true hrem_dc)
      geo_chunk
      rw [hl.h15]
      rfl
    exact ⟨_, accAddr, cls, hrun, hheap⟩
  · simp only [hrem, ↓reduceIte]
    have hrem_dc : ((geoDcmpg absDy (Geometry.absFloat (yb - startY))).toBitVec.sle 0#32) = false := by
      rw [geoDcmpg_fle_iff]; exact decide_eq_false hrem
    have hlen : (encodeCoordPairs acc).size + 1 < 2 ^ 31 := by
      rw [encodeCoordPairs_size]; exact hsz
    have hnneg : (((UInt32.ofNat (encodeCoordPairs acc).size).add (UInt32.ofNat 1)).toBitVec.slt 0#32) = false :=
      array_len_plus1_nneg hlen
    have hidx_nneg : ((UInt32.ofNat (encodeCoordPairs acc).size).toBitVec.slt 0#32) = false :=
      array_len_nneg (by omega)
    let nextY := curY + stepY
    let pairVal : JvmVal := .pair (.boxedInt curX.toUInt32) (.boxedInt nextY.toUInt32)
    let newLen := (UInt32.ofNat (encodeCoordPairs acc).size).add (UInt32.ofNat 1)
    let copied : Array JvmVal := Array.ofFn (n := newLen.toNat)
      (fun i => if h : i.val < (encodeCoordPairs acc).size then (encodeCoordPairs acc)[i.val] else .null)
    let a' := jh.alloc (.objArray cls copied)
    have ha_old : a'.2.get? accAddr = some (.objArray cls (encodeCoordPairs acc)) :=
      get?_alloc_old jh _ hheap
    have ha'_self : a'.2.get? a'.1 = some (.objArray cls copied) :=
      get?_alloc_self jh _
    have ha'_lt : a'.1 < a'.2.objects.size := alloc_fst_lt jh _
    have hidx_lt : (UInt32.ofNat (encodeCoordPairs acc).size).toNat < copied.size := by
      have hnew : newLen.toNat = (encodeCoordPairs acc).size + 1 := by
        change ((UInt32.ofNat (encodeCoordPairs acc).size + UInt32.ofNat 1).toNat) = _
        rw [UInt32.toNat_add]
        change ((encodeCoordPairs acc).size % 2 ^ 32 + 1 % 2 ^ 32) % 2 ^ 32 = _
        omega
      have hold : (UInt32.ofNat (encodeCoordPairs acc).size).toNat = (encodeCoordPairs acc).size := by
        change (encodeCoordPairs acc).size % 2 ^ 32 = _
        omega
      simp [copied, hnew, hold]
    let jh' := a'.2.set a'.1 (.objArray cls (copied.set (UInt32.ofNat (encodeCoordPairs acc).size).toNat pairVal hidx_lt))
    have hpush : copied.set (UInt32.ofNat (encodeCoordPairs acc).size).toNat pairVal hidx_lt =
        encodeCoordPairs (acc.push (curX, nextY)) := by
      rw [array_copy_set_eq_push (encodeCoordPairs acc) pairVal hlen]
      simp [pairVal, encodeCoordPairs, Array.map_push]
    have ha'_in_jh' : jh'.get? a'.1 = some (.objArray cls (encodeCoordPairs (acc.push (curX, nextY)))) := by
      rw [← hpush]
      exact get?_set_self a'.2 a'.1 _ ha'_lt
    have hstep : ∃ (locals' : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 94 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 228
          (f_Geometry_rayMarchLoop___redArg_prog.drop 228)
          { pc := 228, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks (k + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 0
          f_Geometry_rayMarchLoop___redArg_prog
          { pc := 0, stack := [], locals := locals', jvmHeap := jh', heap := () } ∧
        LoopLocals locals' (fuel - 1) startX startY absDx absDy stepX stepY endX endY curX nextY a'.1 := by
      constructor
      apply And.intro
      · rw [show k + 94 + ((fuel - 1).toNat * 250 + 120) = (k + ((fuel - 1).toNat * 250 + 120)) + 94 by omega]
        geo_chunk
        rw [h34, hl.h3]
        geo_step step_absFloat
        geo_chunk
        rw [hl.h7, show yb.sub startY = yb - startY from rfl]
        geo_step step_dcmpg
        geo_branch_step (branch_ifle_false hrem_dc)
        geo_chunk
        rw [hl.h14, hl.h10, hl.h0, asI32_i32, asI32_i32, ui32_add_eq, int32_toUInt32_add]
        geo_step step_uint_ctor
        geo_chunk
        rw [hl.h15]
        geo_step step_intrinsics_checkNotNull
        geo_chunk
        rw [hl.h15]
        geo_step (step_checkcast_objArray hheap)
        geo_chunk
        rw [hl.h15]
        geo_step (step_checkcast_objArray hheap)
        geo_step (step_arraylength hheap)
        geo_chunk
        geo_step (step_arrays_copyOf hnneg hheap)
        geo_chunk
        geo_step step_intrinsics_checkNotNullExpr
        geo_chunk
        rw [hl.h15]
        geo_step (step_checkcast_objArray ha_old)
        geo_step (step_arraylength ha_old)
        geo_step step_newClass_pair
        geo_chunk
        rw [hl.h13]
        geo_step step_integer_valueOf
        geo_chunk
        geo_step step_integer_valueOf
        geo_step step_pair_init
        geo_step (step_aastore hidx_nneg ha'_self hidx_lt)
        geo_chunk
        geo_branch_step (branch_goto_eq rfl)
        exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          dsimp only <;>
          simp [Jvm.setLocal, ui32_sub_eq, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13] <;>
          rfl
    rcases hstep with ⟨loc', heq, hl'⟩
    rw [heq]
    exact hrec k curX nextY loc' jh' a'.1 cls hl' ha'_in_jh'

private theorem int32_toUInt32_eq_iff (a b : Int32) : a.toUInt32 = b.toUInt32 ↔ a = b :=
  ⟨fun h => by
    have hb : a.toBitVec = b.toBitVec := congrArg UInt32.toBitVec h
    cases a; cases b
    have h1 := congrArg Int32.ofBitVec hb
    simpa using h1,
   fun h => by subst h; rfl⟩

private theorem ui32_eq_zero_of_toNat_eq_zero {x : UInt32} (h : x.toNat = 0) : x = 0 := by
  have hb : x.toBitVec = (0 : UInt32).toBitVec := BitVec.eq_of_toNat_eq (by simpa using h)
  simpa using congrArg UInt32.ofBitVec hb

private theorem ui32_pred_toNat {x : UInt32} (hx : x ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have hx0 : 0 < x.toNat := Nat.pos_of_ne_zero fun h0 => hx (ui32_eq_zero_of_toNat_eq_zero h0)
  rw [UInt32.toNat_sub_of_le x 1 (by simpa [UInt32.le_iff_toNat_le] using Nat.succ_le_of_lt hx0)]
  rfl

private theorem loop_from84
    {k accAddr : Nat} {fuel : UInt32} {startX startY dx dy absDx absDy xb yb : Float}
    {stepX stepY endX endY curX curY : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (h31 : locals 31 = .f64 xb)
    (h34 : locals 34 = .f64 yb)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31)
    (hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + 150 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 84
        (f_Geometry_rayMarchLoop___redArg_prog.drop 84)
        { pc := 84, stack := [], locals := locals, jvmHeap := jh, heap := () })
      (if (stepX == 0) = true then
         let remY := Geometry.absFloat (yb - startY)
         if remY ≥ absDy then acc
         else
           let nextY := curY + stepY
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY curX nextY
             (acc.push (curX, nextY))
       else if (stepY == 0) = true then
         let remX := Geometry.absFloat (xb - startX)
         if remX ≥ absDx then acc
         else
           let nextX := curX + stepX
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX curY
             (acc.push (nextX, curY))
       else
         let remX := Geometry.absFloat (xb - startX)
         let remY := Geometry.absFloat (yb - startY)
         let crossX := remX * absDy
         let crossY := remY * absDx
         let limitCross := absDx * absDy
         let minCross := if crossX < crossY then crossX else crossY
         if minCross ≥ limitCross then acc
         else
           let nextX := if crossX ≤ crossY then curX + stepX else curX
           let nextY := if crossY ≤ crossX then curY + stepY else curY
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY
             (acc.push (nextX, nextY))) := by
  by_cases hsx : stepX = 0
  · have hsxb : (stepX == 0) = true := beq_iff_eq.mpr hsx
    simp only [hsxb, ↓reduceIte]
    have hsx0 : stepX.toUInt32 = 0 := by simp [hsx]; rfl
    have hrun : Jvm.runJvmResFast geomHooks (k + 150 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 84
        (f_Geometry_rayMarchLoop___redArg_prog.drop 84)
        { pc := 84, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks ((k + 54) + 94 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 228
          (f_Geometry_rayMarchLoop___redArg_prog.drop 228)
          { pc := 228, stack := [], locals := locals, jvmHeap := jh, heap := () } := by
      generalize htarget : Jvm.runJvmResFast geomHooks ((k + 54) + 94 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 228
        (f_Geometry_rayMarchLoop___redArg_prog.drop 228)
        { pc := 228, stack := [], locals := locals, jvmHeap := jh, heap := () } = target
      rw [show k + 150 + ((fuel - 1).toNat * 250 + 120) =
        ((k + 54) + 94 + ((fuel - 1).toNat * 250 + 120)) + 2 by omega]
      geo_chunk
      rw [hl.h9]
      geo_branch_step (branch_ifeq_true hsx0)
      exact htarget
    rw [hrun]
    exact loop_from228 hl h34 hheap hsz hrec
  · have hsxb : (stepX == 0) = false := beq_false_of_ne hsx
    simp only [hsxb, Bool.false_eq_true, ↓reduceIte]
    have hsx0 : stepX.toUInt32 ≠ 0 := by
      intro h
      apply hsx
      exact (int32_toUInt32_eq_iff stepX 0).mp h
    by_cases hsy : stepY = 0
    · have hsyb : (stepY == 0) = true := beq_iff_eq.mpr hsy
      simp only [hsyb, ↓reduceIte]
      have hsy0 : stepY.toUInt32 = 0 := by simp [hsy]; rfl
      have hrun : Jvm.runJvmResFast geomHooks (k + 150 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 84
          (f_Geometry_rayMarchLoop___redArg_prog.drop 84)
          { pc := 84, stack := [], locals := locals, jvmHeap := jh, heap := () } =
          Jvm.runJvmResFast geomHooks ((k + 52) + 94 + ((fuel - 1).toNat * 250 + 120))
            f_Geometry_rayMarchLoop___redArg_prog 132
            (f_Geometry_rayMarchLoop___redArg_prog.drop 132)
            { pc := 132, stack := [], locals := locals, jvmHeap := jh, heap := () } := by
        generalize htarget : Jvm.runJvmResFast geomHooks ((k + 52) + 94 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 132
          (f_Geometry_rayMarchLoop___redArg_prog.drop 132)
          { pc := 132, stack := [], locals := locals, jvmHeap := jh, heap := () } = target
        rw [show k + 150 + ((fuel - 1).toNat * 250 + 120) =
          ((k + 52) + 94 + ((fuel - 1).toNat * 250 + 120)) + 4 by omega]
        geo_chunk
        rw [hl.h9]
        geo_branch_step (branch_ifeq_false hsx0)
        geo_chunk
        rw [hl.h10]
        geo_branch_step (branch_ifeq_true hsy0)
        exact htarget
      rw [hrun]
      exact loop_from132 hl h31 hheap hsz hrec
    · have hsyb : (stepY == 0) = false := beq_false_of_ne hsy
      simp only [hsyb, Bool.false_eq_true, ↓reduceIte]
      have hsy0 : stepY.toUInt32 ≠ 0 := by
        intro h
        apply hsy
        exact (int32_toUInt32_eq_iff stepY 0).mp h
      let remX := Geometry.absFloat (xb - startX)
      let remY := Geometry.absFloat (yb - startY)
      let crossX := remX * absDy
      let crossY := remY * absDx
      let limitCross := absDx * absDy
      by_cases hlt : crossX < crossY
      · simp only [show Geometry.absFloat (xb - startX) * absDy < Geometry.absFloat (yb - startY) * absDx from hlt, ↓reduceIte]
        have hlt_dc : ((geoDcmpg crossX crossY).toBitVec.slt 0#32) = true := by
          rw [geoDcmpg_lt_iff]; exact decide_eq_true hlt
        have hrun : ∃ (locals324 : Nat → JvmVal),
            Jvm.runJvmResFast geomHooks (k + 150 + ((fuel - 1).toNat * 250 + 120))
              f_Geometry_rayMarchLoop___redArg_prog 84
              (f_Geometry_rayMarchLoop___redArg_prog.drop 84)
              { pc := 84, stack := [], locals := locals, jvmHeap := jh, heap := () } =
            Jvm.runJvmResFast geomHooks ((k + 1) + 110 + ((fuel - 1).toNat * 250 + 120))
              f_Geometry_rayMarchLoop___redArg_prog 324
              (f_Geometry_rayMarchLoop___redArg_prog.drop 324)
              { pc := 324, stack := [], locals := locals324, jvmHeap := jh, heap := () } ∧
            LoopLocals locals324 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
            (locals324 23 = .f64 limitCross ∧
             locals324 25 = .f64 crossY ∧
             locals324 27 = .f64 crossX ∧
             locals324 29 = .f64 crossX) := by
          constructor
          apply And.intro
          · rw [show k + 150 + ((fuel - 1).toNat * 250 + 120) =
              ((k + 1) + 110 + ((fuel - 1).toNat * 250 + 120)) + 39 by omega]
            geo_chunk
            rw [hl.h9]
            geo_branch_step (branch_ifeq_false hsx0)
            geo_chunk
            rw [hl.h10]
            geo_branch_step (branch_ifeq_false hsy0)
            geo_chunk
            rw [h31, hl.h1]
            geo_step step_absFloat
            geo_chunk
            rw [h34, hl.h3]
            geo_step step_absFloat
            geo_chunk
            rw [hl.h7, hl.h5, show xb.sub startX = xb - startX from rfl, show yb.sub startY = yb - startY from rfl]
            rw [show (JvmVal.f64 absDx).asF64 = absDx from rfl,
                show (JvmVal.f64 absDy).asF64 = absDy from rfl]
            rw [show (Geometry.absFloat (xb - startX)).mul absDy = crossX from rfl,
                show (Geometry.absFloat (yb - startY)).mul absDx = crossY from rfl,
                show absDx.mul absDy = limitCross from rfl]
            geo_step step_dcmpg
            geo_branch_step (branch_iflt_true hlt_dc)
            geo_chunk
            rw [branch_goto_eq rfl]
            try exact runJvmResFast_eq rfl rfl
          · refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩⟩
            · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
            · simp [Jvm.setLocal]; rfl
            · simp [Jvm.setLocal]; rfl
            · simp [Jvm.setLocal]; rfl
            · simp [Jvm.setLocal]; rfl
        rcases hrun with ⟨loc, heq, hl', h23, h25, h27, h29⟩
        rw [heq]
        exact loop_from324 hl' h23 h25 h27 h29 hheap hsz hrec
      · have hlt' : ¬ (Geometry.absFloat (xb - startX) * absDy < Geometry.absFloat (yb - startY) * absDx) := hlt
        simp only [hlt', ↓reduceIte]
        have hlt_dc : ((geoDcmpg crossX crossY).toBitVec.slt 0#32) = false := by
          rw [geoDcmpg_lt_iff]; exact decide_eq_false hlt
        have hrun : ∃ (locals324 : Nat → JvmVal),
            Jvm.runJvmResFast geomHooks (k + 150 + ((fuel - 1).toNat * 250 + 120))
              f_Geometry_rayMarchLoop___redArg_prog 84
              (f_Geometry_rayMarchLoop___redArg_prog.drop 84)
              { pc := 84, stack := [], locals := locals, jvmHeap := jh, heap := () } =
            Jvm.runJvmResFast geomHooks ((k + 1) + 110 + ((fuel - 1).toNat * 250 + 120))
              f_Geometry_rayMarchLoop___redArg_prog 324
              (f_Geometry_rayMarchLoop___redArg_prog.drop 324)
              { pc := 324, stack := [], locals := locals324, jvmHeap := jh, heap := () } ∧
            LoopLocals locals324 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
            (locals324 23 = .f64 limitCross ∧
             locals324 25 = .f64 crossY ∧
             locals324 27 = .f64 crossX ∧
             locals324 29 = .f64 crossY) := by
          constructor
          apply And.intro
          · rw [show k + 150 + ((fuel - 1).toNat * 250 + 120) =
              ((k + 1) + 110 + ((fuel - 1).toNat * 250 + 120)) + 39 by omega]
            geo_chunk
            rw [hl.h9]
            geo_branch_step (branch_ifeq_false hsx0)
            geo_chunk
            rw [hl.h10]
            geo_branch_step (branch_ifeq_false hsy0)
            geo_chunk
            rw [h31, hl.h1]
            geo_step step_absFloat
            geo_chunk
            rw [h34, hl.h3]
            geo_step step_absFloat
            geo_chunk
            rw [hl.h7, hl.h5, show xb.sub startX = xb - startX from rfl, show yb.sub startY = yb - startY from rfl]
            rw [show (JvmVal.f64 absDx).asF64 = absDx from rfl,
                show (JvmVal.f64 absDy).asF64 = absDy from rfl]
            rw [show (Geometry.absFloat (xb - startX)).mul absDy = crossX from rfl,
                show (Geometry.absFloat (yb - startY)).mul absDx = crossY from rfl,
                show absDx.mul absDy = limitCross from rfl]
            geo_step step_dcmpg
            geo_branch_step (branch_iflt_false hlt_dc)
            geo_chunk
            rw [branch_goto_eq rfl]
            try exact runJvmResFast_eq rfl rfl
          · refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩⟩
            · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
            · simp [Jvm.setLocal]; rfl
            · simp [Jvm.setLocal]; rfl
            · simp [Jvm.setLocal]; rfl
            · simp [Jvm.setLocal]; rfl
        rcases hrun with ⟨loc, heq, hl', h23, h25, h27, h29⟩
        rw [heq]
        exact loop_from324 hl' h23 h25 h27 h29 hheap hsz hrec

private theorem loop_from60
    {k accAddr : Nat} {fuel : UInt32} {startX startY dx dy absDx absDy xb : Float}
    {stepX stepY endX endY curX curY : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (h36 : locals 36 = .i32 0)
    (h37 : locals 37 = .f64 xb)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31)
    (hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + 164 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 60
        (f_Geometry_rayMarchLoop___redArg_prog.drop 60)
        { pc := 60, stack := [], locals := locals, jvmHeap := jh, heap := () })
      (let yb := if stepY > 0 then (curY + 1).toFloat else curY.toFloat
       if (stepX == 0) = true then
         let remY := Geometry.absFloat (yb - startY)
         if remY ≥ absDy then acc
         else
           let nextY := curY + stepY
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY curX nextY
             (acc.push (curX, nextY))
       else if (stepY == 0) = true then
         let remX := Geometry.absFloat (xb - startX)
         if remX ≥ absDx then acc
         else
           let nextX := curX + stepX
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX curY
             (acc.push (nextX, curY))
       else
         let remX := Geometry.absFloat (xb - startX)
         let remY := Geometry.absFloat (yb - startY)
         let crossX := remX * absDy
         let crossY := remY * absDx
         let limitCross := absDx * absDy
         let minCross := if crossX < crossY then crossX else crossY
         if minCross ≥ limitCross then acc
         else
           let nextX := if crossX ≤ crossY then curX + stepX else curX
           let nextY := if crossY ≤ crossX then curY + stepY else curY
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY
             (acc.push (nextX, nextY))) := by
  dsimp only
  by_cases hsy : (0 : Int32) < stepY
  · simp only [hsy, ↓reduceIte]
    have hsy_slt : ((0 : UInt32).toBitVec.slt stepY.toUInt32.toBitVec) = true := hsy
    have hrun : ∃ (locals84 : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 164 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 60
          (f_Geometry_rayMarchLoop___redArg_prog.drop 60)
          { pc := 60, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks (k + 150 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 84
          (f_Geometry_rayMarchLoop___redArg_prog.drop 84)
          { pc := 84, stack := [], locals := locals84, jvmHeap := jh, heap := () } ∧
        LoopLocals locals84 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
        (locals84 31 = .f64 xb ∧ locals84 34 = .f64 (curY + 1).toFloat) := by
      constructor
      apply And.intro
      · rw [show k + 164 + ((fuel - 1).toNat * 250 + 120) =
          (k + 150 + ((fuel - 1).toNat * 250 + 120)) + 14 by omega]
        geo_chunk
        rw [h36, hl.h10]
        geo_branch_step (branch_if_icmplt_true hsy_slt)
        geo_chunk_n 11
        rw [hl.h14, h37, h36]
        exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ⟨?_, ?_⟩⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
        · simp [Jvm.setLocal]
        · simp only [Jvm.setLocal]
          rw [asI32_i32, ui32_add_eq]
          rfl
    rcases hrun with ⟨loc, heq, hl', h31, h34⟩
    rw [heq]
    exact loop_from84 hl' h31 h34 hheap hsz hrec
  · simp only [hsy, ↓reduceIte]
    have hsy_slt : ((0 : UInt32).toBitVec.slt stepY.toUInt32.toBitVec) = false := Bool.eq_false_iff.mpr hsy
    have hrun : ∃ (locals84 : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 164 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 60
          (f_Geometry_rayMarchLoop___redArg_prog.drop 60)
          { pc := 60, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks ((k + 1) + 150 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 84
          (f_Geometry_rayMarchLoop___redArg_prog.drop 84)
          { pc := 84, stack := [], locals := locals84, jvmHeap := jh, heap := () } ∧
        LoopLocals locals84 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
        (locals84 31 = .f64 xb ∧ locals84 34 = .f64 curY.toFloat) := by
      constructor
      apply And.intro
      · rw [show k + 164 + ((fuel - 1).toNat * 250 + 120) =
          ((k + 1) + 150 + ((fuel - 1).toNat * 250 + 120)) + 13 by omega]
        geo_chunk
        rw [h36, hl.h10]
        geo_branch_step (branch_if_icmplt_false hsy_slt)
        geo_chunk
        rw [hl.h14, h37, h36]
        rw [branch_goto_eq rfl]
        try exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ⟨?_, ?_⟩⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
        · simp [Jvm.setLocal]
        · simp only [Jvm.setLocal]
          rw [asI32_i32]
          rfl
    rcases hrun with ⟨loc, heq, hl', h31, h34⟩
    rw [heq]
    exact loop_from84 hl' h31 h34 hheap hsz hrec

private theorem loop_from40
    {k accAddr : Nat} {fuel : UInt32} {startX startY dx dy absDx absDy : Float}
    {stepX stepY endX endY curX curY : Int32}
    {locals : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {cls : String}
    {acc : Array (Int32 × Int32)}
    (hl : LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)))
    (hsz : acc.size + 1 < 2 ^ 31)
    (hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + 176 + ((fuel - 1).toNat * 250 + 120))
        f_Geometry_rayMarchLoop___redArg_prog 40
        (f_Geometry_rayMarchLoop___redArg_prog.drop 40)
        { pc := 40, stack := [], locals := locals, jvmHeap := jh, heap := () })
      (let xb := if stepX > 0 then (curX + 1).toFloat else curX.toFloat
       let yb := if stepY > 0 then (curY + 1).toFloat else curY.toFloat
       if (stepX == 0) = true then
         let remY := Geometry.absFloat (yb - startY)
         if remY ≥ absDy then acc
         else
           let nextY := curY + stepY
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY curX nextY
             (acc.push (curX, nextY))
       else if (stepY == 0) = true then
         let remX := Geometry.absFloat (xb - startX)
         if remX ≥ absDx then acc
         else
           let nextX := curX + stepX
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX curY
             (acc.push (nextX, curY))
       else
         let remX := Geometry.absFloat (xb - startX)
         let remY := Geometry.absFloat (yb - startY)
         let crossX := remX * absDy
         let crossY := remY * absDx
         let limitCross := absDx * absDy
         let minCross := if crossX < crossY then crossX else crossY
         if minCross ≥ limitCross then acc
         else
           let nextX := if crossX ≤ crossY then curX + stepX else curX
           let nextY := if crossY ≤ crossX then curY + stepY else curY
           Geometry.rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY
             (acc.push (nextX, nextY))) := by
  dsimp only
  by_cases hsx : (0 : Int32) < stepX
  · simp only [hsx, ↓reduceIte]
    have hsx_slt : ((0 : UInt32).toBitVec.slt stepX.toUInt32.toBitVec) = true := hsx
    have hrun : ∃ (locals60 : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 176 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 40
          (f_Geometry_rayMarchLoop___redArg_prog.drop 40)
          { pc := 40, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks (k + 164 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 60
          (f_Geometry_rayMarchLoop___redArg_prog.drop 60)
          { pc := 60, stack := [], locals := locals60, jvmHeap := jh, heap := () } ∧
        LoopLocals locals60 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
        (locals60 36 = .i32 0 ∧ locals60 37 = .f64 (curX + 1).toFloat) := by
      constructor
      apply And.intro
      · rw [show k + 176 + ((fuel - 1).toNat * 250 + 120) =
          (k + 164 + ((fuel - 1).toNat * 250 + 120)) + 12 by omega]
        geo_chunk
        rw [hl.h9, show (UInt32.ofNat 0) = 0 from rfl]
        geo_branch_step (branch_if_icmplt_true hsx_slt)
        geo_chunk_n 9
        rw [hl.h13]
        exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ⟨?_, ?_⟩⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
        · simp [Jvm.setLocal]
        · simp only [Jvm.setLocal]
          rw [asI32_i32, ui32_add_eq]
          rfl
    rcases hrun with ⟨loc, heq, hl', h36, h37⟩
    rw [heq]
    exact loop_from60 hl' h36 h37 hheap hsz hrec
  · simp only [hsx, ↓reduceIte]
    have hsx_slt : ((0 : UInt32).toBitVec.slt stepX.toUInt32.toBitVec) = false := Bool.eq_false_iff.mpr hsx
    have hrun : ∃ (locals60 : Nat → JvmVal),
        Jvm.runJvmResFast geomHooks (k + 176 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 40
          (f_Geometry_rayMarchLoop___redArg_prog.drop 40)
          { pc := 40, stack := [], locals := locals, jvmHeap := jh, heap := () } =
        Jvm.runJvmResFast geomHooks ((k + 1) + 164 + ((fuel - 1).toNat * 250 + 120))
          f_Geometry_rayMarchLoop___redArg_prog 60
          (f_Geometry_rayMarchLoop___redArg_prog.drop 60)
          { pc := 60, stack := [], locals := locals60, jvmHeap := jh, heap := () } ∧
        LoopLocals locals60 fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr ∧
        (locals60 36 = .i32 0 ∧ locals60 37 = .f64 curX.toFloat) := by
      constructor
      apply And.intro
      · rw [show k + 176 + ((fuel - 1).toNat * 250 + 120) =
          ((k + 1) + 164 + ((fuel - 1).toNat * 250 + 120)) + 11 by omega]
        geo_chunk
        rw [hl.h9, show (UInt32.ofNat 0) = 0 from rfl]
        geo_branch_step (branch_if_icmplt_false hsx_slt)
        geo_chunk
        rw [hl.h13]
        rw [branch_goto_eq rfl]
        try exact runJvmResFast_eq rfl rfl
      · refine ⟨?_, ⟨?_, ?_⟩⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
        · simp [Jvm.setLocal]
        · simp only [Jvm.setLocal]
          rw [asI32_i32]
          rfl
    rcases hrun with ⟨loc, heq, hl', h36, h37⟩
    rw [heq]
    exact loop_from60 hl' h36 h37 hheap hsz hrec

private def rayMarchZeroLocals (locals : Nat → JvmVal) : Nat → JvmVal :=
  Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal
    (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal
      (Jvm.setLocal (Jvm.setLocal locals 16 (.i32 0)) 17 (.i32 0))
      18 (.f64 0.0)) 20 (.f64 0.0)) 22 (.i32 0)) 23 (.f64 0.0)) 25 (.f64 0.0))
    27 (.f64 0.0)) 29 (.f64 0.0)) 31 (.f64 0.0)) 33 (.i32 0)) 34 (.f64 0.0))
  36 (.i32 0)) 37 (.f64 0.0)

private theorem rayMarchLoop_fuel_zero
    (k accAddr : Nat) (startX startY absDx absDy : Float)
    (stepX stepY endX endY curX curY : Int32)
    (locals : Nat → JvmVal) (jh : Jvm.JvmHeap Empty) (cls : String)
    (acc : Array (Int32 × Int32))
    (hl : LoopLocals locals 0 startX startY absDx absDy stepX stepY endX endY curX curY accAddr)
    (hheap : jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc))) :
    LoopResultOk
      (Jvm.runJvmResFast geomHooks (k + (0 : UInt32).toNat * 250 + 120)
        f_Geometry_rayMarchLoop___redArg_prog 0
        f_Geometry_rayMarchLoop___redArg_prog
        { pc := 0, stack := [], locals := locals, jvmHeap := jh, heap := () })
      acc := by
  have hrun :
      Jvm.runJvmResFast geomHooks (k + (0 : UInt32).toNat * 250 + 120)
        f_Geometry_rayMarchLoop___redArg_prog 0
        f_Geometry_rayMarchLoop___redArg_prog
        { pc := 0, stack := [], locals := locals, jvmHeap := jh, heap := () } =
      some (.heapRef accAddr,
        { pc := 39, stack := [.heapRef accAddr], locals := rayMarchZeroLocals locals, jvmHeap := jh, heap := () }) := by
    rw [show k + (0 : UInt32).toNat * 250 + 120 = (k + 88) + 32 by simp]
    geo_chunk
    rw [hl.h0]
    geo_branch_step (branch_ifeq_true rfl)
    geo_chunk
    rw [hl.h15]
    rfl
  exact ⟨_, accAddr, cls, hrun, hheap⟩

private theorem rayMarchLoop_from0 :
    ∀ (n k accAddr : Nat) (fuel : UInt32) (startX startY dx dy absDx absDy : Float)
      (stepX stepY endX endY curX curY : Int32)
      (locals : Nat → JvmVal) (jh : Jvm.JvmHeap Empty) (cls : String)
      (acc : Array (Int32 × Int32)),
      fuel.toNat ≤ n →
      LoopLocals locals fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr →
      jh.get? accAddr = some (Jvm.HeapObj.objArray cls (encodeCoordPairs acc)) →
      acc.size + fuel.toNat < 2 ^ 31 →
      LoopResultOk
        (Jvm.runJvmResFast geomHooks (k + fuel.toNat * 250 + 120)
          f_Geometry_rayMarchLoop___redArg_prog 0
          f_Geometry_rayMarchLoop___redArg_prog
          { pc := 0, stack := [], locals := locals, jvmHeap := jh, heap := () })
        (Geometry.rayMarchLoop fuel startX startY dx dy absDx absDy stepX stepY endX endY curX curY acc) := by
  intro n
  induction n with
  | zero =>
    intro k accAddr fuel startX startY dx dy absDx absDy stepX stepY endX endY curX curY locals jh cls acc
      hfn hl hheap hbound
    have hfuel : fuel = 0 := ui32_eq_zero_of_toNat_eq_zero (by omega)
    subst hfuel
    rw [Geometry.rayMarchLoop.eq_1]
    simp only [beq_self_eq_true, ↓reduceIte]
    exact rayMarchLoop_fuel_zero k accAddr startX startY absDx absDy stepX stepY endX endY curX curY
      locals jh cls acc hl hheap
  | succ n ih =>
    intro k accAddr fuel startX startY dx dy absDx absDy stepX stepY endX endY curX curY locals jh cls acc
      hfn hl hheap hbound
    rw [Geometry.rayMarchLoop.eq_1]
    by_cases hfuel : fuel = 0
    · subst hfuel
      simp only [beq_self_eq_true, ↓reduceIte]
      exact rayMarchLoop_fuel_zero k accAddr startX startY absDx absDy stepX stepY endX endY curX curY
        locals jh cls acc hl hheap
    · have hfb : (fuel == 0) = false := beq_false_of_ne hfuel
      simp only [hfb, Bool.false_eq_true, ↓reduceIte]
      have hpred : (fuel - 1).toNat = fuel.toNat - 1 := ui32_pred_toNat hfuel
      have hfuel_pos : 0 < fuel.toNat :=
        Nat.pos_of_ne_zero fun h0 => hfuel (ui32_eq_zero_of_toNat_eq_zero h0)
      have hfn' : (fuel - 1).toNat ≤ n := by omega
      have hsz : acc.size + 1 < 2 ^ 31 := by omega
      have hrec : LoopRecHyp fuel startX startY dx dy absDx absDy stepX stepY endX endY acc := by
        intro k0 nx ny loc' jh' addr' cls' hl' hheap'
        exact ih k0 addr' (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nx ny
          loc' jh' cls' (acc.push (nx, ny)) hfn' hl' hheap' (by simp; omega)
      by_cases hdone : (curX == endX && curY == endY) = true
      · simp only [hdone, ↓reduceIte]
        have hx : curX = endX := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hdone
          exact hdone.1
        have hy : curY = endY := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hdone
          exact hdone.2
        have hx_u : curX.toUInt32 = endX.toUInt32 := by rw [hx]
        have hy_u : curY.toUInt32 = endY.toUInt32 := by rw [hy]
        have hrun :
            Jvm.runJvmResFast geomHooks (k + fuel.toNat * 250 + 120)
              f_Geometry_rayMarchLoop___redArg_prog 0
              f_Geometry_rayMarchLoop___redArg_prog
              { pc := 0, stack := [], locals := locals, jvmHeap := jh, heap := () } =
            some (.heapRef accAddr,
              { pc := 37, stack := [.heapRef accAddr], locals := rayMarchZeroLocals locals, jvmHeap := jh, heap := () }) := by
          rw [show k + fuel.toNat * 250 + 120 = (k + fuel.toNat * 250 + 82) + 38 by omega]
          geo_chunk
          rw [hl.h0]
          geo_branch_step (branch_ifeq_false hfuel)
          geo_chunk
          rw [hl.h13, hl.h11]
          geo_branch_step (branch_if_icmpne_false hx_u)
          geo_chunk
          rw [hl.h14, hl.h12]
          geo_branch_step (branch_if_icmpne_false hy_u)
          geo_chunk
          rw [hl.h15]
          rfl
        exact ⟨_, accAddr, cls, hrun, hheap⟩
      · have hdonef : (curX == endX && curY == endY) = false := Bool.eq_false_iff.mpr hdone
        simp only [hdonef, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : curX = endX
        · have hy : curY ≠ endY := by
            intro h
            apply hdone
            simp [hx, h]
          have hx_u : curX.toUInt32 = endX.toUInt32 := by rw [hx]
          have hy_u : curY.toUInt32 ≠ endY.toUInt32 := by
            intro h
            exact hy ((int32_toUInt32_eq_iff curY endY).mp h)
          have heq :
              Jvm.runJvmResFast geomHooks (k + fuel.toNat * 250 + 120)
                f_Geometry_rayMarchLoop___redArg_prog 0
                f_Geometry_rayMarchLoop___redArg_prog
                { pc := 0, stack := [], locals := locals, jvmHeap := jh, heap := () } =
              Jvm.runJvmResFast geomHooks ((k + 38) + 176 + ((fuel - 1).toNat * 250 + 120))
                f_Geometry_rayMarchLoop___redArg_prog 40
                (f_Geometry_rayMarchLoop___redArg_prog.drop 40)
                { pc := 40, stack := [], locals := rayMarchZeroLocals locals, jvmHeap := jh, heap := () } := by
            rw [show k + fuel.toNat * 250 + 120 =
                ((k + 38) + 176 + ((fuel - 1).toNat * 250 + 120)) + 36 by omega]
            geo_chunk
            rw [hl.h0]
            geo_branch_step (branch_ifeq_false hfuel)
            geo_chunk
            rw [hl.h13, hl.h11]
            geo_branch_step (branch_if_icmpne_false hx_u)
            geo_chunk
            rw [hl.h14, hl.h12]
            geo_branch_step (branch_if_icmpne_true hy_u)
            exact runJvmResFast_eq rfl rfl
          have hl40 : LoopLocals (rayMarchZeroLocals locals) fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [rayMarchZeroLocals, Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
          rw [heq]
          exact loop_from40 hl40 hheap hsz hrec
        · have hx_u : curX.toUInt32 ≠ endX.toUInt32 := by
            intro h
            exact hx ((int32_toUInt32_eq_iff curX endX).mp h)
          have heq :
              Jvm.runJvmResFast geomHooks (k + fuel.toNat * 250 + 120)
                f_Geometry_rayMarchLoop___redArg_prog 0
                f_Geometry_rayMarchLoop___redArg_prog
                { pc := 0, stack := [], locals := locals, jvmHeap := jh, heap := () } =
              Jvm.runJvmResFast geomHooks ((k + 41) + 176 + ((fuel - 1).toNat * 250 + 120))
                f_Geometry_rayMarchLoop___redArg_prog 40
                (f_Geometry_rayMarchLoop___redArg_prog.drop 40)
                { pc := 40, stack := [], locals := rayMarchZeroLocals locals, jvmHeap := jh, heap := () } := by
            rw [show k + fuel.toNat * 250 + 120 =
                ((k + 41) + 176 + ((fuel - 1).toNat * 250 + 120)) + 33 by omega]
            geo_chunk
            rw [hl.h0]
            geo_branch_step (branch_ifeq_false hfuel)
            geo_chunk
            rw [hl.h13, hl.h11]
            geo_branch_step (branch_if_icmpne_true hx_u)
            exact runJvmResFast_eq rfl rfl
          have hl40 : LoopLocals (rayMarchZeroLocals locals) fuel startX startY absDx absDy stepX stepY endX endY curX curY accAddr := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [rayMarchZeroLocals, Jvm.setLocal, hl.h0, hl.h1, hl.h3, hl.h5, hl.h7, hl.h9, hl.h10, hl.h11, hl.h12, hl.h13, hl.h14, hl.h15]
          rw [heq]
          exact loop_from40 hl40 hheap hsz hrec

theorem rayMarchLoop_equiv (fuel : UInt32) (startX startY dx dy absDx absDy : Float)
    (stepX stepY endX endY curX curY : Int32) (acc : Array (Int32 × Int32))
    (hbound : acc.size + fuel.toNat < 2 ^ 31) :
    let a0 := ({} : Jvm.JvmHeap Empty).alloc
      (.objArray "[Ljava/lang/Object;" (encodeCoordPairs acc))
    let st0 := initJvmState
      [ (0, .i32 fuel), (1, .f64 startX), (3, .f64 startY), (5, .f64 absDx),
        (7, .f64 absDy), (9, .i32 stepX.toUInt32), (10, .i32 stepY.toUInt32),
        (11, .i32 endX.toUInt32), (12, .i32 endY.toUInt32), (13, .i32 curX.toUInt32),
        (14, .i32 curY.toUInt32), (15, .heapRef a0.1) ] a0.2
    ∃ (st' : JvmState) (resAddr : Nat) (resCls : String),
      Jvm.runJvmRes geomHooks (fuel.toNat * 250 + 120)
        f_Geometry_rayMarchLoop___redArg_prog st0 =
          some (.heapRef resAddr, st') ∧
      st'.jvmHeap.get? resAddr = some (Jvm.HeapObj.objArray resCls (encodeCoordPairs
        (Geometry.rayMarchLoop fuel startX startY dx dy absDx absDy stepX stepY endX endY curX curY acc))) := by
  intro a0 st0
  have ha0 : a0.2.get? a0.1 = some (.objArray "[Ljava/lang/Object;" (encodeCoordPairs acc)) := by
    simpa [a0] using get?_alloc_self ({} : Jvm.JvmHeap Empty) (.objArray "[Ljava/lang/Object;" (encodeCoordPairs acc))
  have hl0 : LoopLocals st0.locals fuel startX startY absDx absDy stepX stepY endX endY curX curY a0.1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [st0, initJvmState, Jvm.initJvmState, List.foldl, Jvm.setLocal]
  have hmain := rayMarchLoop_from0 fuel.toNat 0 a0.1 fuel startX startY dx dy absDx absDy
    stepX stepY endX endY curX curY st0.locals a0.2 "[Ljava/lang/Object;" acc (Nat.le_refl _) hl0 ha0 hbound
  rcases hmain with ⟨st', resAddr, resCls, hres, hget⟩
  refine ⟨st', resAddr, resCls, ?_, hget⟩
  rw [Jvm.runJvmRes_of_runJvmResFast0 geomHooks _ _ _ _ rfl]
  rw [Nat.zero_add] at hres
  rw [show (st0 : JvmState) = { pc := 0, stack := [], locals := st0.locals, jvmHeap := a0.2, heap := () } from rfl]
  exact hres

end RayMarchLoop

end Geometry.JvmVerification

open Lean in
private def isJvmBvCheckAxiom (env : Environment) (a : Name) : Bool :=
  let named := match a with
    | .str (.str (.str _ "_native") "bv_decide") _ => true
    | _ => false
  named && match env.find? a with
    | some (.axiomInfo info) =>
      info.type.isAppOfArity ``Eq 3 &&
        (info.type.getArg! 1).isAppOf `Std.Tactic.BVDecide.Reflect.verifyBVExpr &&
        (info.type.getArg! 2).isConstOf ``Bool.true
    | _ => false

open Lean Elab Command in
elab "#audit_jvm_equiv_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut provenProgs : NameSet := {}
  for (n, ci) in env.constants.toList do
    unless `Geometry.JvmVerification |>.isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    count := count + 1
    for c in ci.type.getUsedConstants do
      if `Geometry.JvmBytecode |>.isPrefixOf c then
        provenProgs := provenProgs.insert c
    let axioms ← liftCoreM <| Lean.collectAxioms n
    let bad := axioms.filter (fun a => !allowed.contains a && !isJvmBvCheckAxiom env a)
    unless bad.isEmpty do
      logError m!"JVM equivalence theorem {n} depends on non-standard axioms: {bad.toList}"
  if count == 0 then
    logError "no JVM equivalence theorems found"
  for (n, ci) in env.constants.toList do
    unless `Geometry.JvmBytecode |>.isPrefixOf n do continue
    unless ci matches .defnInfo _ do continue
    if n.isInternal then continue
    if n.toString.endsWith "_prog" && !provenProgs.contains n then
      logError m!"lifted JVM program {n} has no equivalence theorem in Geometry.JvmVerification"

#audit_jvm_equiv_axioms
