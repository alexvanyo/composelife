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

import KotlinJvmBytecode
import models.GameOfLifeStepModel
import proofs.KotlinJvmEquiv.AlgKotlinProgs

/-!
# JVM equivalence of `GameOfLifeStep.kt`

`stepGeneration_equiv` and `stepGenerations_equiv` prove that the lifted `GameOfLifeStepKt_stepGeneration_prog` and
`GameOfLifeStepKt_stepGenerations_prog` compute `stepGenerationModel` / `stepGenerationsModel` under `mkAlgKotlinHooks`.

A `Set<IntOffset>` is a modeled collection (`IsColl`): an instance `{arr}` whose object array holds boxed
`IntOffset`s (`encV`, packed as `IntOffset(x, y)` packs them) in iteration order. Inputs are `java/util/Set` or
`LinkedHashSet` collections of distinct cells (`alive.Nodup`, as for any `Set`). The proofs step the bytecode
instruction by instruction (`Reaches`): the `flatMapTo` loop, `addAll(aliveCells)`, then the `filterTo` loop with the
inner `count { it in aliveCells }` loop. `getMooreNeighbors` is the `JvmSemantics` hook that copies geometry's
`getMooreNeighborsModel` (proved there against the `:geometry` bytecode); `LinkedHashSet` / iterator / `addAll` /
`contains` / `isEmpty` are the `JvmSemantics` collection hooks. `stepGenerations` calls the lifted `stepGeneration`
program through `resolveProg`.
-/

namespace Algorithm.KotlinJvmVerification
open Algorithm.JvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

namespace GolStep

/-! ## Bounded reachability -/

/-- `st` runs to `st'` in at most `B` steps (and exactly the same number for every extra fuel). -/
def Reaches (H : Jvm.JvmHooks AlgExt AlgHeap) (prog : List JvmInstr) (st st' : JvmState) (B : Nat) : Prop :=
  ∃ n, n ≤ B ∧ ∀ F, Jvm.runJvmRes H (F + n) prog st = Jvm.runJvmRes H F prog st'

variable {H : Jvm.JvmHooks AlgExt AlgHeap} {prog : List JvmInstr}

theorem reaches_refl {st : JvmState} {B : Nat} : Reaches H prog st st B :=
  ⟨0, Nat.zero_le _, fun _ => rfl⟩

theorem reaches_of_eq {st st' : JvmState} {B : Nat} (h : st = st') : Reaches H prog st st' B :=
  h ▸ reaches_refl

theorem reaches_trans {st1 st2 st3 : JvmState} {B1 B2 : Nat}
    (h1 : Reaches H prog st1 st2 B1) (h2 : Reaches H prog st2 st3 B2) : Reaches H prog st1 st3 (B2 + B1) := by
  obtain ⟨n1, hn1, hr1⟩ := h1
  obtain ⟨n2, hn2, hr2⟩ := h2
  refine ⟨n2 + n1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc, hr1, hr2]

theorem reaches_mono {st st' : JvmState} {B B' : Nat} (h : Reaches H prog st st' B) (hle : B ≤ B') :
    Reaches H prog st st' B' := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, by omega, hr⟩

theorem reaches_step {st st' st'' : JvmState} {instr : JvmInstr} {B : Nat}
    (hget : prog[st.pc]? = some instr) (hnb : Jvm.isBranchInstr instr = false)
    (hs : Jvm.stepInstr H instr st = .inl (some st')) (h : Reaches H prog st' st'' B) :
    Reaches H prog st st'' (B + 1) := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n + 1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc, Jvm.runJvmRes_nonbranch H (F + n) prog st instr hget hnb, hs]
  exact hr F

theorem reaches_goto {st st'' : JvmState} {t B : Nat}
    (hget : prog[st.pc]? = some (.goto t)) (h : Reaches H prog { st with pc := t } st'' B) :
    Reaches H prog st st'' (B + 1) := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n + 1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc]
  simp only [Jvm.runJvmRes, hget]
  exact hr F

/-- The default `isZero?` (`algKotlinHooksWith` keeps it). -/
def DefaultZero (H : Jvm.JvmHooks AlgExt AlgHeap) : Prop :=
  ∀ v : JvmVal, H.isZero? v = (Jvm.JvmVal.asI32? v).map (· == 0)

theorem reaches_ifeq {st st'' : JvmState} {t B : Nat} {v : UInt32} {rest : List JvmVal} (hz : DefaultZero H)
    (hget : prog[st.pc]? = some (.ifeq t)) (hstk : st.stack = .i32 v :: rest)
    (h : Reaches H prog
      (if v = 0 then { st with pc := t, stack := rest } else { st with pc := st.pc + 1, stack := rest })
      st'' B) :
    Reaches H prog st st'' (B + 1) := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n + 1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc, ← hr F]
  simp only [Jvm.runJvmRes, hget, hstk]
  rw [hz]
  by_cases hv : v = 0
  · simp [hv, Jvm.JvmVal.asI32?]
  · have hb : (v == 0) = false := by simpa using hv
    simp [hv, hb, Jvm.JvmVal.asI32?]

theorem reaches_ifge {st st'' : JvmState} {t B : Nat} {v : UInt32} {rest : List JvmVal}
    (hget : prog[st.pc]? = some (.ifge t)) (hstk : st.stack = .i32 v :: rest)
    (h : Reaches H prog (if (0#32).sle v.toBitVec then { st with pc := t, stack := rest }
      else { st with pc := st.pc + 1, stack := rest }) st'' B) :
    Reaches H prog st st'' (B + 1) := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n + 1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc, ← hr F]
  simp only [Jvm.runJvmRes, hget, hstk, Jvm.JvmVal.asI32?]
  split <;> rfl

theorem reaches_ifgt {st st'' : JvmState} {t B : Nat} {v : UInt32} {rest : List JvmVal}
    (hget : prog[st.pc]? = some (.ifgt t)) (hstk : st.stack = .i32 v :: rest)
    (h : Reaches H prog (if (0#32).slt v.toBitVec then { st with pc := t, stack := rest }
      else { st with pc := st.pc + 1, stack := rest }) st'' B) :
    Reaches H prog st st'' (B + 1) := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n + 1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc, ← hr F]
  simp only [Jvm.runJvmRes, hget, hstk, Jvm.JvmVal.asI32?]
  split <;> rfl

theorem reaches_if_icmpeq {st st'' : JvmState} {t B : Nat} {a b : UInt32} {rest : List JvmVal}
    (hget : prog[st.pc]? = some (.if_icmpeq t)) (hstk : st.stack = .i32 b :: .i32 a :: rest)
    (h : Reaches H prog (if a = b then { st with pc := t, stack := rest }
      else { st with pc := st.pc + 1, stack := rest }) st'' B) :
    Reaches H prog st st'' (B + 1) := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n + 1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc, ← hr F]
  simp only [Jvm.runJvmRes, hget, hstk, Jvm.JvmVal.asI32?]
  by_cases hab : a = b <;> simp [hab]

theorem reaches_if_icmpne {st st'' : JvmState} {t B : Nat} {a b : UInt32} {rest : List JvmVal}
    (hget : prog[st.pc]? = some (.if_icmpne t)) (hstk : st.stack = .i32 b :: .i32 a :: rest)
    (h : Reaches H prog (if a = b then { st with pc := st.pc + 1, stack := rest }
      else { st with pc := t, stack := rest }) st'' B) :
    Reaches H prog st st'' (B + 1) := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n + 1, by omega, fun F => ?_⟩
  rw [← Nat.add_assoc, ← hr F]
  simp only [Jvm.runJvmRes, hget, hstk, Jvm.JvmVal.asI32?]
  by_cases hab : a = b <;> simp [hab]

section Branches
variable {pc t B : Nat} {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
  {stE : JvmState}

theorem reaches_ifeq_fall {v : UInt32} (hz : DefaultZero H) (hget : prog[pc]? = some (.ifeq t)) (hv : v ≠ 0)
    (h : Reaches H prog ⟨pc + 1, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 v :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_ifeq hz hget rfl (by rw [ite_eq_right hv]; exact h)

theorem reaches_ifeq_jump {v : UInt32} (hz : DefaultZero H) (hget : prog[pc]? = some (.ifeq t)) (hv : v = 0)
    (h : Reaches H prog ⟨t, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 v :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_ifeq hz hget rfl (by rw [ite_eq_left hv]; exact h)

theorem reaches_ifge_jump {v : UInt32} (hget : prog[pc]? = some (.ifge t)) (hv : (0#32).sle v.toBitVec = true)
    (h : Reaches H prog ⟨t, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 v :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_ifge hget rfl (by rw [ite_eq_left hv]; exact h)

theorem reaches_ifgt_jump {v : UInt32} (hget : prog[pc]? = some (.ifgt t)) (hv : (0#32).slt v.toBitVec = true)
    (h : Reaches H prog ⟨t, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 v :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_ifgt hget rfl (by rw [ite_eq_left hv]; exact h)

theorem reaches_ifgt_fall {v : UInt32} (hget : prog[pc]? = some (.ifgt t)) (hv : (0#32).slt v.toBitVec = false)
    (h : Reaches H prog ⟨pc + 1, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 v :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_ifgt hget rfl (by rw [ite_eq_right (by simp [hv])]; exact h)

theorem reaches_if_icmpeq_jump {a b : UInt32} (hget : prog[pc]? = some (.if_icmpeq t)) (hv : a = b)
    (h : Reaches H prog ⟨t, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_if_icmpeq hget rfl (by rw [ite_eq_left hv]; exact h)

theorem reaches_if_icmpeq_fall {a b : UInt32} (hget : prog[pc]? = some (.if_icmpeq t)) (hv : a ≠ b)
    (h : Reaches H prog ⟨pc + 1, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_if_icmpeq hget rfl (by rw [ite_eq_right hv]; exact h)

theorem reaches_if_icmpne_jump {a b : UInt32} (hget : prog[pc]? = some (.if_icmpne t)) (hv : a ≠ b)
    (h : Reaches H prog ⟨t, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_if_icmpne hget rfl (by rw [ite_eq_right hv]; exact h)

theorem reaches_if_icmpne_fall {a b : UInt32} (hget : prog[pc]? = some (.if_icmpne t)) (hv : a = b)
    (h : Reaches H prog ⟨pc + 1, rest, locs, jh, hp⟩ stE B) :
    Reaches H prog ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩ stE (B + 1) :=
  reaches_if_icmpne hget rfl (by rw [ite_eq_left hv]; exact h)

theorem reaches_congr_locs {L L' : Nat → JvmVal} {stk : List JvmVal} (hL : L = L')
    (h : Reaches H prog ⟨pc, stk, L', jh, hp⟩ stE B) : Reaches H prog ⟨pc, stk, L, jh, hp⟩ stE B := hL ▸ h

end Branches

theorem run_of_reaches_ret {st st' : JvmState} {B fuel : Nat} {v : JvmVal}
    (h : Reaches H prog st st' B) (hget : prog[st'.pc]? = some .areturn) (hstk : st'.stack = v :: rest)
    (hfuel : B + 1 ≤ fuel) :
    Jvm.runJvmRes H fuel prog st = some (v, st') := by
  obtain ⟨n, hn, hr⟩ := h
  obtain ⟨F, rfl⟩ : ∃ F, fuel = (F + 1) + n := ⟨fuel - n - 1, by omega⟩
  rw [hr]
  rw [Jvm.runJvmRes_nonbranch H F prog st' .areturn hget rfl]
  have hs : Jvm.stepInstr H .areturn st' = .inr (some v) := by
    unfold Jvm.stepInstr
    rw [hstk]
  rw [hs]

/-! ## Encoding of cells as boxed `IntOffset`s -/

/-- The packed `IntOffset` of a cell, as `IntOffset(x, y)` and `:geometry` pack it. -/
def pk (c : Int32 × Int32) : UInt64 := geomPackOffset c.1 c.2

/-- A cell as a boxed `IntOffset`. -/
def encV (c : Int32 × Int32) : JvmVal := .ext (.intOffset (pk c))

/-- Cells as boxed `IntOffset`s, in order. -/
def enc (l : List (Int32 × Int32)) : List JvmVal := l.map encV

/-- `LinkedHashSet.add` on cells: append unless present. -/
def ins (acc : List (Int32 × Int32)) (x : Int32 × Int32) : List (Int32 × Int32) :=
  if acc.contains x then acc else acc ++ [x]

theorem int32_toUInt32_inj {a b : Int32} (h : a.toUInt32 = b.toUInt32) : a = b := by
  cases a; cases b; cases h; rfl

theorem uint32_toInt32_inj {a b : UInt32} (h : a.toInt32 = b.toInt32) : a = b := by
  cases a; cases b
  injection h with h'

theorem geomOffsetX_pack (x y : Int32) : geomOffsetX (geomPackOffset x y) = x := by
  rcases x with ⟨⟨bx⟩⟩
  rcases y with ⟨⟨by_⟩⟩
  apply int32_toUInt32_inj
  apply congrArg UInt32.ofBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((((BitVec.setWidth 64 bx) <<< 32) ||| (BitVec.setWidth 64 by_)) >>> 32).setWidth 32).getLsbD i =
    bx.getLsbD i
  have hi64 : i < 64 := by omega
  have h1 : 32 + i < 64 := by omega
  have h2 : ¬ (32 + i < 32) := by omega
  have h3 : 32 + i - 32 = i := by omega
  simp [hi, hi64, h1, h2, h3]

theorem geomOffsetY_pack (x y : Int32) : geomOffsetY (geomPackOffset x y) = y := by
  rcases x with ⟨⟨bx⟩⟩
  rcases y with ⟨⟨by_⟩⟩
  apply int32_toUInt32_inj
  apply congrArg UInt32.ofBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((((BitVec.setWidth 64 bx) <<< 32) ||| (BitVec.setWidth 64 by_)).setWidth 32)).getLsbD i =
    by_.getLsbD i
  simp [hi]

theorem pk_inj {a b : Int32 × Int32} (h : pk a = pk b) : a = b := by
  have hx := congrArg geomOffsetX h
  have hy := congrArg geomOffsetY h
  simp only [pk, geomOffsetX_pack, geomOffsetY_pack] at hx hy
  exact Prod.ext hx hy

theorem pk_beq (a b : Int32 × Int32) : (pk a == pk b) = (a == b) := by
  by_cases h : a = b
  · subst h; rw [beq_self_eq_true, beq_self_eq_true]
  · have : pk a ≠ pk b := fun h' => h (pk_inj h')
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem encV_equals (a b : Int32 × Int32) : algKotlinEquals (encV a) (encV b) = (a == b) := by
  show algKotlinBeqExt (.intOffset (pk a)) (.intOffset (pk b)) = (a == b)
  exact pk_beq a b

theorem enc_any_equals (l : List (Int32 × Int32)) (x : Int32 × Int32) :
    (enc l).any (fun y => algKotlinEquals (encV x) y) = l.contains x := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [enc, List.map_cons, List.any_cons, List.contains_cons] at ih ⊢
    rw [ih, encV_equals]

theorem enc_toArray_any (l : List (Int32 × Int32)) (x : Int32 × Int32) :
    (enc l).toArray.any (fun y => algKotlinEquals (encV x) y) = l.contains x := by
  rw [List.any_toArray, enc_any_equals]

theorem enc_ins (acc : List (Int32 × Int32)) (x : Int32 × Int32) :
    enc (ins acc x) = if acc.contains x then enc acc else enc acc ++ [encV x] := by
  unfold ins; split <;> simp [enc]

theorem dedup_enc_of_nodup : ∀ (acc l : List (Int32 × Int32)), (acc ++ l).Nodup →
    (enc l).foldl (fun a x => if a.any (fun y => algKotlinEquals x y) then a else a ++ [x]) (enc acc) =
      enc (acc ++ l)
  | acc, [], _ => by simp [enc]
  | acc, x :: l, hnd => by
    have hx : x ∉ acc := by
      intro hm
      have := (List.nodup_append.mp hnd).2.2 x hm x (List.mem_cons_self ..)
      exact this rfl
    have hc : (enc acc).any (fun y => algKotlinEquals (encV x) y) = false := by
      rw [enc_any_equals]; simpa using hx
    simp only [enc, List.map_cons, List.foldl_cons] at hc ⊢
    rw [show (List.map encV acc).any (fun y => algKotlinEquals (encV x) y) = false from hc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := dedup_enc_of_nodup (acc ++ [x]) l (by simpa using hnd)
    simpa [enc] using this

theorem geomAdd_pk (c : Int32 × Int32) (dx dy : Int32) :
    geomAddPackedOffset (geomPackOffset dx dy) (pk c) = pk (c.1 + dx, c.2 + dy) := by
  simp only [geomAddPackedOffset, pk, geomOffsetX_pack, geomOffsetY_pack, Int32.add_comm]

theorem moore_pk (c : Int32 × Int32) :
    geomGetMooreNeighborsModel (pk c) = (mooreNeighbors32 c).map pk := by
  simp only [geomGetMooreNeighborsModel, geomMooreNeighborOffsets, mooreNeighbors32, mooreDeltas32, addOffset32,
    List.map_cons, List.map_nil, geomAdd_pk]

theorem moore_nodup (c : Int32 × Int32) : (mooreNeighbors32 c).Nodup := by
  have hinj : ∀ a b : Int32 × Int32, addOffset32 c a = addOffset32 c b → a = b := by
    intro a b h
    simp only [addOffset32, Prod.mk.injEq, Int32.add_right_inj] at h
    exact Prod.ext h.1 h.2
  have hd : mooreDeltas32.Nodup := by decide
  unfold mooreNeighbors32
  exact List.Pairwise.map (addOffset32 c) (fun a b hab h => hab (hinj a b h)) hd

theorem moore_elems (c : Int32 × Int32) :
    Jvm.dedupJvmVals algKotlinEquals (encodeIntOffsets (geomGetMooreNeighborsModel (pk c))).toList =
      enc (mooreNeighbors32 c) := by
  have h1 : (encodeIntOffsets (geomGetMooreNeighborsModel (pk c))).toList = enc (mooreNeighbors32 c) := by
    simp [encodeIntOffsets, moore_pk, enc, encV]
  rw [h1]
  have := dedup_enc_of_nodup [] (mooreNeighbors32 c) (by simpa using moore_nodup c)
  simpa [Jvm.dedupJvmVals, enc] using this

/-! ## Heap facts -/

/-- A `java/util/Iterator` over the object array at `arr`, at index `k`. -/
def iterObj (arr : Nat) (k : UInt32) : Jvm.HeapObj AlgExt :=
  .instance "java/util/Iterator" [("arr", .heapRef arr), ("idx", .i32 k)]

/-- `addr` holds a modeled collection of class `cls` whose backing array `arr` (of element class `ec`) holds the
cells `l` as boxed `IntOffset`s. -/
def IsColl (jh : Jvm.JvmHeap AlgExt) (addr : Nat) (cls : String) (arr : Nat) (ec : String)
    (l : List (Int32 × Int32)) : Prop :=
  jh.get? addr = some (.instance cls [("arr", .heapRef arr)]) ∧ jh.get? arr = some (.objArray ec (enc l).toArray)

/-- `jh` extends `jh0`: every object of `jh0` is unchanged. -/
def Frame (jh0 jh : Jvm.JvmHeap AlgExt) : Prop :=
  jh0.objects.size ≤ jh.objects.size ∧ ∀ a, a < jh0.objects.size → jh.get? a = jh0.get? a

theorem frame_refl (jh : Jvm.JvmHeap AlgExt) : Frame jh jh := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem frame_trans {a b c : Jvm.JvmHeap AlgExt} (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

theorem heap_set_size (h : Jvm.JvmHeap AlgExt) (a : Nat) (o : Jvm.HeapObj AlgExt) :
    (h.set a o).objects.size = h.objects.size := by
  unfold Jvm.JvmHeap.set; split <;> simp

theorem heap_alloc_size (h : Jvm.JvmHeap AlgExt) (o : Jvm.HeapObj AlgExt) :
    (h.alloc o).2.objects.size = h.objects.size + 1 := by
  simp [Jvm.JvmHeap.alloc]

theorem frame_alloc (h : Jvm.JvmHeap AlgExt) (o : Jvm.HeapObj AlgExt) : Frame h (h.alloc o).2 :=
  ⟨by rw [heap_alloc_size]; omega, fun _ hx => Jvm.jvmHeap_get?_alloc_old h o hx⟩

theorem frame_set {jh0 h : Jvm.JvmHeap AlgExt} {a : Nat} (o : Jvm.HeapObj AlgExt) (hf : Frame jh0 h)
    (ha : jh0.objects.size ≤ a) : Frame jh0 (h.set a o) :=
  ⟨by rw [heap_set_size]; exact hf.1, fun x hx => by
    rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega), hf.2 x hx]⟩

theorem heap_set_set (h : Jvm.JvmHeap AlgExt) (a : Nat) (v w : Jvm.HeapObj AlgExt) :
    (h.set a v).set a w = h.set a w := by
  unfold Jvm.JvmHeap.set
  by_cases hlt : a < h.objects.size
  · simp [hlt, Array.set_set]
  · simp [hlt]

theorem heap_set_get_self {h : Jvm.JvmHeap AlgExt} {a : Nat} {v : Jvm.HeapObj AlgExt} (hg : h.get? a = some v) :
    h.set a v = h := by
  have hlt := Jvm.jvmHeap_get?_some_lt hg
  unfold Jvm.JvmHeap.set
  simp only [hlt, ↓reduceDIte]
  cases h with
  | mk objs st =>
    simp only [Jvm.JvmHeap.get?] at hg hlt ⊢
    congr 1
    apply Array.ext
    · simp
    · intro i hi1 hi2
      by_cases hia : a = i
      · subst hia; simp only [Array.getElem_set_self]
        rw [Array.getElem?_eq_getElem hlt] at hg
        exact (Option.some.inj hg).symm
      · rw [Array.getElem_set_ne _ _ hia]

theorem heap_get_set_self_lt {h : Jvm.JvmHeap AlgExt} {a : Nat} {w : Jvm.HeapObj AlgExt}
    (hlt : a < h.objects.size) : (h.set a w).get? a = some w := by
  simp [Jvm.JvmHeap.set, Jvm.JvmHeap.get?, hlt]

/-- The heap after `allocAlgKotlinColl jh cls elems`. -/
def collHeap (jh : Jvm.JvmHeap AlgExt) (cls : String) (elems : Array JvmVal) : Jvm.JvmHeap AlgExt :=
  ((jh.alloc (.objArray "java/lang/Object" elems)).2.alloc
    (.instance cls [("arr", .heapRef jh.objects.size)])).2

theorem allocColl_eq (jh : Jvm.JvmHeap AlgExt) (cls : String) (elems : Array JvmVal) :
    allocAlgKotlinColl jh cls elems = (jh.objects.size + 1, collHeap jh cls elems) := by
  simp [allocAlgKotlinColl, collHeap, Jvm.JvmHeap.alloc]

theorem collHeap_size (jh : Jvm.JvmHeap AlgExt) (cls : String) (elems : Array JvmVal) :
    (collHeap jh cls elems).objects.size = jh.objects.size + 2 := by
  simp [collHeap, Jvm.JvmHeap.alloc]

theorem collHeap_get_inst (jh : Jvm.JvmHeap AlgExt) (cls : String) (elems : Array JvmVal) :
    (collHeap jh cls elems).get? (jh.objects.size + 1) =
      some (.instance cls [("arr", .heapRef jh.objects.size)]) := by
  show ((jh.objects.push _).push _)[jh.objects.size + 1]? = _
  rw [Array.getElem?_push]
  simp

theorem collHeap_get_arr (jh : Jvm.JvmHeap AlgExt) (cls : String) (elems : Array JvmVal) :
    (collHeap jh cls elems).get? jh.objects.size = some (.objArray "java/lang/Object" elems) := by
  simp [collHeap, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, Array.getElem?_push]

theorem collHeap_get_old (jh : Jvm.JvmHeap AlgExt) (cls : String) (elems : Array JvmVal) {a : Nat}
    (ha : a < jh.objects.size) : (collHeap jh cls elems).get? a = jh.get? a := by
  simp only [collHeap]
  rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [heap_alloc_size]; omega), Jvm.jvmHeap_get?_alloc_old _ _ ha]

theorem frame_collHeap (jh : Jvm.JvmHeap AlgExt) (cls : String) (elems : Array JvmVal) :
    Frame jh (collHeap jh cls elems) :=
  ⟨by rw [collHeap_size]; omega, fun _ hx => collHeap_get_old jh cls elems hx⟩

theorem isColl_collHeap (jh : Jvm.JvmHeap AlgExt) (cls : String) (l : List (Int32 × Int32)) :
    IsColl (collHeap jh cls (enc l).toArray) (jh.objects.size + 1) cls jh.objects.size "java/lang/Object" l :=
  ⟨collHeap_get_inst .., collHeap_get_arr ..⟩

theorem isColl_frame {jh jh' : Jvm.JvmHeap AlgExt} {a arr : Nat} {cls ec : String} {l : List (Int32 × Int32)}
    (hf : Frame jh jh') (hc : IsColl jh a cls arr ec l) : IsColl jh' a cls arr ec l :=
  ⟨by rw [hf.2 a (Jvm.jvmHeap_get?_some_lt hc.1)]; exact hc.1,
    by rw [hf.2 arr (Jvm.jvmHeap_get?_some_lt hc.2)]; exact hc.2⟩

theorem algKotlinColl?_of {jh : Jvm.JvmHeap AlgExt} {a arr : Nat} {cls ec : String} {l : List (Int32 × Int32)}
    (hc : IsColl jh a cls arr ec l) (hcls : isAlgKotlinCollClass cls = true) :
    algKotlinColl? jh a = some (cls, arr, ec, (enc l).toArray) := by
  simp [algKotlinColl?, hc.1, hc.2, hcls]

/-- `addAll` of cells into a `LinkedHashSet` of cells. -/
theorem collAddAll_lhs : ∀ (xs acc : List (Int32 × Int32)) (jh : Jvm.JvmHeap AlgExt) (c ca : Nat) (ec : String),
    IsColl jh c "java/util/LinkedHashSet" ca ec acc → c ≠ ca →
    ∃ chg, algKotlinCollAddAll jh c (enc xs) =
      some (chg, jh.set ca (.objArray ec (enc (xs.foldl ins acc)).toArray))
  | [], acc, jh, c, ca, ec, hc, _ => ⟨false, by
    show some (false, jh) = some (false, jh.set ca (.objArray ec (enc acc).toArray))
    rw [heap_set_get_self hc.2]⟩
  | x :: xs, acc, jh, c, ca, ec, hc, hne => by
    have hadd : algKotlinCollAdd jh c (encV x) =
        some (!(acc.contains x), jh.set ca (.objArray ec (enc (ins acc x)).toArray)) := by
      simp only [algKotlinCollAdd, algKotlinColl?_of hc rfl]
      simp only [enc_toArray_any, enc_ins]
      cases hx : acc.contains x
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, List.push_toArray]
        rfl
      · simp only [↓reduceIte, Bool.not_true]
        rw [heap_set_get_self hc.2]
        rfl
    have hc' : IsColl (jh.set ca (.objArray ec (enc (ins acc x)).toArray)) c "java/util/LinkedHashSet" ca ec
        (ins acc x) :=
      ⟨by rw [Jvm.jvmHeap_get?_set_ne _ _ hne]; exact hc.1, Jvm.jvmHeap_get?_set_self hc.2⟩
    obtain ⟨chg, hrec⟩ := collAddAll_lhs xs (ins acc x) _ c ca ec hc' hne
    refine ⟨!(acc.contains x) || chg, ?_⟩
    show algKotlinCollAddAll jh c (encV x :: enc xs) = _
    simp only [algKotlinCollAddAll]
    rw [hadd]
    simp only
    rw [hrec, heap_set_set, List.foldl_cons]

/-! ## Hook steps under `algKotlinHooksWith` -/

section HookSteps

variable {ip : String → JvmState → List (Nat × JvmVal) → Option (Option (JvmVal × JvmState))}
  {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}

theorem defaultZero_hw : DefaultZero (algKotlinHooksWith ip) := fun _ => rfl

theorem stepInstr_iface (c m d : String) (st : JvmState) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface c m d) st =
      Jvm.stepInvokeInterfaceGeneric (algKotlinHooksWith ip) st c m d := rfl

theorem stepInstr_static (c m d : String) (st : JvmState) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokestatic c m d) st =
      Jvm.stepInvokeStaticGeneric (algKotlinHooksWith ip) st c m d := rfl

theorem stepInstr_special (c m d : String) (st : JvmState) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokespecial c m d) st =
      Jvm.stepInvokeSpecialGeneric (algKotlinHooksWith ip) st c m d := rfl

theorem hw_iface_leaf (st : JvmState) (c m d : String)
    (h : ∀ cls, st.stack[(Jvm.parseMethodParamTags d).length]? ≠ some (.allocRef cls)) :
    (algKotlinHooksWith ip).stepInvokeInterface st c m d = algKotlinStepInterfaceLeaf st c m d := by
  simp only [algKotlinHooksWith]
  all_goals (split <;> first | rfl | (exfalso; exact h _ ‹_›))

theorem step_checkcast_inst {a : Nat} {cls ocls : String} {fields : List (String × JvmVal)}
    (hg : jh.get? a = some (.instance ocls fields)) (hsub : algKotlinIsSubtypeOf ocls cls = true) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.checkcast cls) ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef a :: stk, locs, jh, hp⟩) := by
  have hc : Jvm.evalCheckCast (algKotlinHooksWith ip) jh cls (.heapRef a) = some (.heapRef a) := by
    simp only [Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, hg,
      Jvm.HeapObj.matchesType]
    have : (algKotlinHooksWith ip).isSubtypeOf = algKotlinIsSubtypeOf := rfl
    rw [this, hsub]; simp
  unfold Jvm.stepInstr
  dsimp only
  rw [hc]

theorem step_instanceof_inst {a : Nat} {cls ocls : String} {fields : List (String × JvmVal)}
    (hg : jh.get? a = some (.instance ocls fields)) (hsub : algKotlinIsSubtypeOf ocls cls = true) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.instanceof cls) ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 1 :: stk, locs, jh, hp⟩) := by
  have hc : Jvm.evalInstanceOf (algKotlinHooksWith ip) jh cls (.heapRef a) = true := by
    simp only [Jvm.evalInstanceOf, Jvm.JvmHeap.checkInstanceOf, hg, Jvm.HeapObj.matchesType]
    have : (algKotlinHooksWith ip).isSubtypeOf = algKotlinIsSubtypeOf := rfl
    rw [this, hsub]; simp
  unfold Jvm.stepInstr
  dsimp only
  rw [hc]; rfl

theorem step_iterator {a arr : Nat} {cls ec : String} {l : List (Int32 × Int32)}
    (hc : IsColl jh a cls arr ec l) (hcls : cls = "java/util/Set" ∨ cls = "java/util/LinkedHashSet") :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;")
        ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stk, locs, (jh.alloc (iterObj arr 0)).2, hp⟩) := by
  rw [stepInstr_iface]
  rcases hcls with rfl | rfl
  · simp [Jvm.stepInvokeInterfaceGeneric, Jvm.extractListArray?, hc.1, hc.2, iterObj]
    rfl
  · have hl : Jvm.extractListArray? jh a = none := by simp [Jvm.extractListArray?, hc.1]
    simp only [Jvm.stepInvokeInterfaceGeneric, hl]
    rw [hw_iface_leaf _ _ _ _ (by intro cls; simp [show (Jvm.parseMethodParamTags "()Ljava/util/Iterator;").length = 0
      from rfl])]
    simp only [algKotlinStepInterfaceLeaf, algKotlinColl?_of hc rfl]
    rfl

theorem step_hasNext {it arr : Nat} {k : UInt32} {ec : String} {es : Array JvmVal}
    (hit : jh.get? it = some (iterObj arr k)) (harr : jh.get? arr = some (.objArray ec es)) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface "java/util/Iterator" "hasNext" "()Z")
        ⟨pc, .heapRef it :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if k.toNat < es.size then 1 else 0) :: stk, locs, jh, hp⟩) := by
  rw [stepInstr_iface]
  simp [Jvm.stepInvokeInterfaceGeneric, hit, harr, iterObj]

theorem step_next {it arr : Nat} {k : UInt32} {ec : String} {es : Array JvmVal}
    (hit : jh.get? it = some (iterObj arr k)) (harr : jh.get? arr = some (.objArray ec es))
    (hlt : k.toNat < es.size) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;")
        ⟨pc, .heapRef it :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, es[k.toNat] :: stk, locs, jh.set it (iterObj arr (k + 1)), hp⟩) := by
  rw [stepInstr_iface]
  simp [Jvm.stepInvokeInterfaceGeneric, hit, harr, iterObj, hlt]

theorem step_moore (c : Int32 × Int32) :
    Jvm.stepInstr (algKotlinHooksWith ip)
        (.invokestatic "com/alexvanyo/composelife/geometry/GeometryExtensionsKt" "getMooreNeighbors--gyyYBs"
          "(J)Ljava/util/Set;")
        ⟨pc, .i64 (pk c) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef (jh.objects.size + 1) :: stk, locs,
        collHeap jh "java/util/LinkedHashSet" (enc (mooreNeighbors32 c)).toArray, hp⟩) := by
  have h : Jvm.stepInstr (algKotlinHooksWith ip)
      (.invokestatic "com/alexvanyo/composelife/geometry/GeometryExtensionsKt" "getMooreNeighbors--gyyYBs"
        "(J)Ljava/util/Set;")
      ⟨pc, .i64 (pk c) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef (allocAlgKotlinColl jh "java/util/LinkedHashSet"
          (Jvm.dedupJvmVals algKotlinEquals (encodeIntOffsets (geomGetMooreNeighborsModel (pk c))).toList).toArray).1
            :: stk, locs,
        (allocAlgKotlinColl jh "java/util/LinkedHashSet"
          (Jvm.dedupJvmVals algKotlinEquals (encodeIntOffsets (geomGetMooreNeighborsModel (pk c))).toList).toArray).2,
          hp⟩) := rfl
  rw [h, moore_elems, allocColl_eq]

theorem hw_static_leaf (st : JvmState) (c m d : String) (h : isAlgKotlinLiftedClass c = false) :
    (algKotlinHooksWith ip).stepInvokeStatic st c m d = algKotlinStepStaticLeaf st c m d := by
  simp only [algKotlinHooksWith, h, Bool.false_eq_true, ↓reduceIte]

theorem hw_special_leaf (st : JvmState) (c m d : String) (h : isAlgKotlinLiftedClass c = false) :
    (algKotlinHooksWith ip).stepInvokeSpecial st c m d = algKotlinStepSpecialLeaf st c m d := by
  simp only [algKotlinHooksWith, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem step_newLHS :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokespecial "java/util/LinkedHashSet" "<init>" "()V")
        ⟨pc, .allocRef "java/util/LinkedHashSet" :: .allocRef "java/util/LinkedHashSet" :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef (jh.objects.size + 1) :: stk, locs,
        collHeap jh "java/util/LinkedHashSet" (enc []).toArray, hp⟩) := by
  rw [stepInstr_special]
  simp only [Jvm.stepInvokeSpecialGeneric]
  rw [hw_special_leaf _ _ _ _ rfl]
  simp only [algKotlinStepSpecialLeaf, allocColl_eq]
  rfl

/-- `CollectionsKt.addAll(dst, src)` of a collection of cells into a `LinkedHashSet` of cells, then `pop`. -/
theorem step_staticAddAll {src sa c ca : Nat} {scls sec ec : String} {xs acc : List (Int32 × Int32)}
    (hs : IsColl jh src scls sa sec xs) (hscls : isAlgKotlinCollClass scls = true)
    (hc : IsColl jh c "java/util/LinkedHashSet" ca ec acc) (hne : c ≠ ca) :
    ∃ b, Jvm.stepInstr (algKotlinHooksWith ip)
        (.invokestatic "kotlin/collections/CollectionsKt" "addAll" "(Ljava/util/Collection;Ljava/lang/Iterable;)Z")
        ⟨pc, .heapRef src :: .heapRef c :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 b :: stk, locs, jh.set ca (.objArray ec (enc (xs.foldl ins acc)).toArray), hp⟩) := by
  obtain ⟨chg, hadd⟩ := collAddAll_lhs xs acc jh c ca ec hc hne
  refine ⟨if chg then 1 else 0, ?_⟩
  rw [stepInstr_static]
  simp only [Jvm.stepInvokeStaticGeneric]
  rw [hw_static_leaf _ _ _ _ rfl]
  simp only [algKotlinStepStaticLeaf, algKotlinColl?_of hs hscls, hadd]
  rfl

theorem step_ifaceAddAll {src sa c ca : Nat} {scls sec ec : String} {xs acc : List (Int32 × Int32)}
    (hs : IsColl jh src scls sa sec xs) (hscls : isAlgKotlinCollClass scls = true)
    (hc : IsColl jh c "java/util/LinkedHashSet" ca ec acc) (hne : c ≠ ca) :
    ∃ b, Jvm.stepInstr (algKotlinHooksWith ip)
        (.invokeinterface "java/util/Set" "addAll" "(Ljava/util/Collection;)Z")
        ⟨pc, .heapRef src :: .heapRef c :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 b :: stk, locs, jh.set ca (.objArray ec (enc (xs.foldl ins acc)).toArray), hp⟩) := by
  obtain ⟨chg, hadd⟩ := collAddAll_lhs xs acc jh c ca ec hc hne
  refine ⟨if chg then 1 else 0, ?_⟩
  rw [stepInstr_iface]
  simp only [Jvm.stepInvokeInterfaceGeneric]
  rw [hw_iface_leaf _ _ _ _ (by intro cls; simp [show (Jvm.parseMethodParamTags "(Ljava/util/Collection;)Z").length = 1
      from rfl])]
  simp only [algKotlinStepInterfaceLeaf, algKotlinColl?_of hs hscls, hadd]
  rfl

theorem step_contains {s sa : Nat} {scls sec : String} {l : List (Int32 × Int32)} (x : Int32 × Int32)
    (hs : IsColl jh s scls sa sec l) (hscls : isAlgKotlinCollClass scls = true) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface "java/util/Set" "contains" "(Ljava/lang/Object;)Z")
        ⟨pc, encV x :: .heapRef s :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if l.contains x then 1 else 0) :: stk, locs, jh, hp⟩) := by
  rw [stepInstr_iface]
  simp only [Jvm.stepInvokeInterfaceGeneric]
  rw [hw_iface_leaf _ _ _ _ (by intro cls; simp [show (Jvm.parseMethodParamTags "(Ljava/lang/Object;)Z").length = 1
      from rfl])]
  simp only [algKotlinStepInterfaceLeaf, algKotlinColl?_of hs hscls, enc_toArray_any]
  rfl

theorem step_isEmpty {m ma : Nat} {mcls mec : String} {l : List (Int32 × Int32)}
    (hm : IsColl jh m mcls ma mec l) (hmcls : isAlgKotlinCollClass mcls = true) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface "java/util/Collection" "isEmpty" "()Z")
        ⟨pc, .heapRef m :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if l.isEmpty then 1 else 0) :: stk, locs, jh, hp⟩) := by
  rw [stepInstr_iface]
  simp only [Jvm.stepInvokeInterfaceGeneric]
  rw [hw_iface_leaf _ _ _ _ (by intro cls; simp [show (Jvm.parseMethodParamTags "()Z").length = 0 from rfl])]
  simp only [algKotlinStepInterfaceLeaf, algKotlinColl?_of hm hmcls]
  cases l <;> rfl

theorem step_add {r ra : Nat} {ec : String} {acc : List (Int32 × Int32)} (x : Int32 × Int32)
    (hr : IsColl jh r "java/util/LinkedHashSet" ra ec acc) (hne : r ≠ ra) :
    ∃ b, Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z")
        ⟨pc, encV x :: .heapRef r :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 b :: stk, locs, jh.set ra (.objArray ec (enc (ins acc x)).toArray), hp⟩) := by
  obtain ⟨chg, hadd⟩ := collAddAll_lhs [x] acc jh r ra ec hr hne
  have hadd1 : algKotlinCollAdd jh r (encV x) = some (chg, jh.set ra (.objArray ec (enc (ins acc x)).toArray)) := by
    simp only [algKotlinCollAddAll, enc, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hadd
    revert hadd
    cases algKotlinCollAdd jh r (encV x) with
    | none => intro h; cases h
    | some p =>
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq, Bool.or_false] at h
      obtain ⟨h1, h2⟩ := h
      cases p with
      | mk b hh =>
        simp only at h1 h2
        subst h1; subst h2; rfl
  refine ⟨if chg then 1 else 0, ?_⟩
  rw [stepInstr_iface]
  have hnot : jh.get? r = some (.instance "java/util/LinkedHashSet" [("arr", .heapRef ra)]) := hr.1
  simp only [Jvm.stepInvokeInterfaceGeneric, hnot]
  rw [hw_iface_leaf _ _ _ _ (by intro cls; simp [show (Jvm.parseMethodParamTags "(Ljava/lang/Object;)Z").length = 1
      from rfl])]
  simp only [algKotlinStepInterfaceLeaf, hadd1]
  rfl

end HookSteps

/-! ## `stepGeneration` -/

/-- One non-branching step whose hook result is computed by `rfl`. -/
macro "gs" : tactic => `(tactic| (refine reaches_step rfl rfl rfl ?_; try dsimp only))
/-- One non-branching step whose hook result is given by a lemma. -/
macro "gsh " h:term : tactic => `(tactic| (refine reaches_step rfl rfl $h ?_; try dsimp only))
/-- A `goto`. -/
macro "gsg" : tactic => `(tactic| (refine reaches_goto rfl ?_; try dsimp only))

section StepGeneration

variable {ip : String → JvmState → List (Nat × JvmVal) → Option (Option (JvmVal × JvmState))} {hp : AlgHeap}

local notation "HW" => algKotlinHooksWith ip
local notation "P" => GameOfLifeStepKt_stepGeneration_prog
local notation "LHS" => "java/util/LinkedHashSet"

/-- Locals at the head of the first loop (`aliveCells.flatMapTo(...)`, pc 18). -/
def locs1 (base : Nat → JvmVal) (s c it : Nat) : Nat → JvmVal :=
  Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal base 0 (.heapRef s)) 2 (.heapRef s)) 3
    (.heapRef c)) 4 (.i32 0)) 5 (.heapRef it)

theorem setCls_sub (scls : String) (hscls : scls = "java/util/Set" ∨ scls = LHS) (t : String)
    (ht : t = "java/lang/Iterable" ∨ t = "java/util/Collection") : algKotlinIsSubtypeOf scls t = true := by
  rcases hscls with rfl | rfl <;> rcases ht with rfl | rfl <;> rfl

theorem gol_prologue (base : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s sa : Nat} {scls sec : String}
    {alive : List (Int32 × Int32)}
    (hs : IsColl jh s scls sa sec alive) (hscls : scls = "java/util/Set" ∨ scls = LHS) :
    Reaches HW P ⟨0, [], Jvm.setLocal base 0 (.heapRef s), jh, hp⟩
      ⟨18, [], locs1 base s (jh.objects.size + 1) (jh.objects.size + 2),
        ((collHeap jh LHS (enc []).toArray).alloc (iterObj sa 0)).2, hp⟩ 18 := by
  gs; gs; gs; gs
  gsh step_checkcast_inst hs.1 (setCls_sub scls hscls _ (.inl rfl))
  gs; gs; gs
  gsh step_newLHS
  gsh step_checkcast_inst (collHeap_get_inst ..) rfl
  gsh step_checkcast_inst (collHeap_get_inst ..) rfl
  gs; gs; gs; gs; gs
  gsh step_iterator (isColl_frame (frame_collHeap ..) hs) hscls
  gs
  rw [collHeap_size]
  exact reaches_refl

/-- Cells collected by the first loop after `k` iterations. -/
def p1 (alive : List (Int32 × Int32)) (k : Nat) : List (Int32 × Int32) :=
  ((alive.take k).flatMap mooreNeighbors32).foldl ins []

theorem p1_succ (alive : List (Int32 × Int32)) (k : Nat) (hk : k < alive.length) :
    p1 alive (k + 1) = (mooreNeighbors32 alive[k]).foldl ins (p1 alive k) := by
  unfold p1
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.foldl_append]

theorem ofNat_toNat_of_lt {k : Nat} (hk : k < 2 ^ 32) : (UInt32.ofNat k).toNat = k := by
  simp [Nat.mod_eq_of_lt hk]

theorem ofNat_succ (k : Nat) : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
  apply UInt32.toNat.inj
  simp [UInt32.toNat_add, UInt32.toNat_ofNat, Nat.add_mod]

theorem hasNext_ne {k : Nat} {l : List (Int32 × Int32)} (hk : k < l.length) (h32 : l.length < 2 ^ 32) :
    (if (UInt32.ofNat k).toNat < (enc l).toArray.size then (1 : UInt32) else 0) ≠ 0 := by
  rw [ofNat_toNat_of_lt (by omega)]
  simp [enc, hk]

theorem hasNext_eq {l : List (Int32 × Int32)} (h32 : l.length < 2 ^ 32) :
    (if (UInt32.ofNat l.length).toNat < (enc l).toArray.size then (1 : UInt32) else 0) = 0 := by
  rw [ofNat_toNat_of_lt h32]
  simp [enc]

theorem enc_get {l : List (Int32 × Int32)} {k : Nat} (hk : k < l.length) (h32 : l.length < 2 ^ 32)
    (hlt : (UInt32.ofNat k).toNat < (enc l).toArray.size) :
    (enc l).toArray[(UInt32.ofNat k).toNat]'hlt = encV l[k] := by
  simp only [ofNat_toNat_of_lt (show k < 2 ^ 32 by omega)]
  simp [enc]

theorem enc_size_lt {l : List (Int32 × Int32)} {k : Nat} (hk : k < l.length) (h32 : l.length < 2 ^ 32) :
    (UInt32.ofNat k).toNat < (enc l).toArray.size := by
  rw [ofNat_toNat_of_lt (by omega)]; simpa [enc] using hk

/-- The heap after one iteration of the first loop on cell `a`. -/
def heap1 (jh : Jvm.JvmHeap AlgExt) (it sa ca : Nat) (k : Nat) (a : Int32 × Int32)
    (acc : List (Int32 × Int32)) : Jvm.JvmHeap AlgExt :=
  (collHeap (jh.set it (iterObj sa (UInt32.ofNat k + 1))) LHS (enc (mooreNeighbors32 a)).toArray).set ca
    (.objArray "java/lang/Object" (enc ((mooreNeighbors32 a).foldl ins acc)).toArray)

theorem locs1_self {L : Nat → JvmVal} {s c it : Nat} (h0 : L 0 = .heapRef s) (h2 : L 2 = .heapRef s)
    (h3 : L 3 = .heapRef c) (h4 : L 4 = .i32 0) (h5 : L 5 = .heapRef it) : locs1 L s c it = L := by
  funext i
  simp only [locs1, Jvm.setLocal]
  repeat' split
  all_goals (subst_vars; first | rfl | exact h0.symm | exact h2.symm | exact h3.symm | exact h4.symm |
    exact h5.symm)

theorem step_next' {ip : String → JvmState → List (Nat × JvmVal) → Option (Option (JvmVal × JvmState))}
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {it arr : Nat} {k : UInt32} {ec : String} {es : Array JvmVal} {v : JvmVal}
    (hit : jh.get? it = some (iterObj arr k)) (harr : jh.get? arr = some (.objArray ec es))
    (hlt : k.toNat < es.size) (hv : es[k.toNat] = v) :
    Jvm.stepInstr (algKotlinHooksWith ip) (.invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;")
        ⟨pc, .heapRef it :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: stk, locs, jh.set it (iterObj arr (k + 1)), hp⟩) := by
  rw [step_next hit harr hlt, hv]

theorem gol_loop1_body (base : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s sa c ca it : Nat} {scls sec : String}
    {alive acc : List (Int32 × Int32)} {k : Nat}
    (hs : IsColl jh s scls sa sec alive)
    (hc : IsColl jh c LHS ca "java/lang/Object" acc) (hit : jh.get? it = some (iterObj sa (UInt32.ofNat k)))
    (hk : k < alive.length) (h32 : alive.length < 2 ^ 32)
    (hc_ca : c ≠ ca) (hit_c : it ≠ c) (hit_ca : it ≠ ca) :
    ∃ L, Reaches HW P ⟨18, [], locs1 base s c it, jh, hp⟩ ⟨18, [], L, heap1 jh it sa ca k alive[k] acc, hp⟩ 21 ∧
      locs1 L s c it = L := by
  have hlt := enc_size_lt hk h32
  let jh1 := jh.set it (iterObj sa (UInt32.ofNat k + 1))
  have hc1 : IsColl jh1 c LHS ca "java/lang/Object" acc :=
    ⟨by rw [Jvm.jvmHeap_get?_set_ne _ _ (Ne.symm hit_c)]; exact hc.1,
      by rw [Jvm.jvmHeap_get?_set_ne _ _ (Ne.symm hit_ca)]; exact hc.2⟩
  have hc2 := isColl_frame (frame_collHeap jh1 LHS (enc (mooreNeighbors32 alive[k])).toArray) hc1
  have hm2 := isColl_collHeap jh1 LHS (mooreNeighbors32 alive[k])
  obtain ⟨b, hb⟩ := step_staticAddAll (ip := ip) (pc := 18 + 18) (stk := []) (locs := Jvm.setLocal (Jvm.setLocal
    (Jvm.setLocal (Jvm.setLocal (locs1 base s c it) 6 (encV alive[k])) 7 (.i64 (pk alive[k]))) 9 (.i32 0)) 10
    (.heapRef (jh1.objects.size + 1))) (hp := hp) hm2 rfl hc2 hc_ca
  refine ⟨Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (locs1 base s c it) 6 (encV alive[k])) 7
    (.i64 (pk alive[k]))) 9 (.i32 0)) 10 (.heapRef (jh1.objects.size + 1)), ?_, ?_⟩
  gs
  gsh step_hasNext hit hs.2
  refine reaches_ifeq_fall defaultZero_hw rfl (hasNext_ne hk h32) ?_
  gs
  gsh step_next' hit hs.2 hlt (enc_get hk h32 hlt)
  gs; gs; gs; gs; gs; gs; gs; gs
  gsh step_moore alive[k]
  gsh step_checkcast_inst (collHeap_get_inst ..) rfl
  gs; gs; gs
  gsh hb
  gs
  gsg
  exact reaches_refl
  exact locs1_self rfl rfl rfl rfl rfl

theorem heap1_frame {jh0 jh : Jvm.JvmHeap AlgExt} {it sa ca k : Nat} {a : Int32 × Int32}
    {acc : List (Int32 × Int32)} (hf : Frame jh0 jh) (hit0 : jh0.objects.size ≤ it)
    (hca0 : jh0.objects.size ≤ ca) : Frame jh0 (heap1 jh it sa ca k a acc) :=
  frame_set _ (frame_trans (frame_set _ hf hit0) (frame_collHeap ..)) hca0

theorem heap1_get_old {jh : Jvm.JvmHeap AlgExt} {it sa ca k x : Nat} {a : Int32 × Int32}
    {acc : List (Int32 × Int32)} (hx : x < jh.objects.size) (hxit : x ≠ it) (hxca : x ≠ ca) :
    (heap1 jh it sa ca k a acc).get? x = jh.get? x := by
  unfold heap1
  rw [Jvm.jvmHeap_get?_set_ne _ _ hxca, collHeap_get_old _ _ _ (by rw [heap_set_size]; exact hx),
    Jvm.jvmHeap_get?_set_ne _ _ hxit]

theorem heap1_get_it {jh : Jvm.JvmHeap AlgExt} {it sa ca k : Nat} {a : Int32 × Int32}
    {acc : List (Int32 × Int32)} (hit : jh.get? it = some (iterObj sa (UInt32.ofNat k))) (hitca : it ≠ ca) :
    (heap1 jh it sa ca k a acc).get? it = some (iterObj sa (UInt32.ofNat (k + 1))) := by
  unfold heap1
  rw [Jvm.jvmHeap_get?_set_ne _ _ hitca, collHeap_get_old _ _ _ (by
    rw [heap_set_size]; exact Jvm.jvmHeap_get?_some_lt hit), Jvm.jvmHeap_get?_set_self hit, ofNat_succ]

theorem heap1_get_ca {jh : Jvm.JvmHeap AlgExt} {it sa ca k : Nat} {a : Int32 × Int32}
    {acc : List (Int32 × Int32)} (hca : jh.get? ca = some (.objArray "java/lang/Object" (enc acc).toArray)) :
    (heap1 jh it sa ca k a acc).get? ca =
      some (.objArray "java/lang/Object" (enc ((mooreNeighbors32 a).foldl ins acc)).toArray) := by
  unfold heap1
  apply heap_get_set_self_lt
  rw [collHeap_size, heap_set_size]
  have := Jvm.jvmHeap_get?_some_lt hca
  omega

theorem gol_loop1 {jh0 : Jvm.JvmHeap AlgExt} {s sa c ca it : Nat} {scls sec : String}
    {alive : List (Int32 × Int32)}
    (hs0 : IsColl jh0 s scls sa sec alive) (h32 : alive.length < 2 ^ 32)
    (hc_ca : c ≠ ca) (hit_c : it ≠ c) (hit_ca : it ≠ ca)
    (hca0 : jh0.objects.size ≤ ca) (hit0 : jh0.objects.size ≤ it) :
    ∀ rem k base jh, k + rem = alive.length → Frame jh0 jh →
      IsColl jh c LHS ca "java/lang/Object" (p1 alive k) → jh.get? it = some (iterObj sa (UInt32.ofNat k)) →
      ∃ L jh', Reaches HW P ⟨18, [], locs1 base s c it, jh, hp⟩ ⟨39, [], locs1 L s c it, jh', hp⟩ (rem * 21 + 3) ∧
        Frame jh0 jh' ∧ IsColl jh' c LHS ca "java/lang/Object" (p1 alive alive.length) ∧
        jh'.get? it = some (iterObj sa (UInt32.ofNat alive.length)) := by
  intro rem
  induction rem with
  | zero =>
    intro k base jh hk hf hc hit
    have hk' : k = alive.length := by omega
    subst hk'
    refine ⟨base, jh, ?_, hf, hc, hit⟩
    have hs := isColl_frame hf hs0
    gs
    gsh step_hasNext hit hs.2
    refine reaches_ifeq_jump defaultZero_hw rfl (hasNext_eq h32) ?_
    exact reaches_refl
  | succ rem ih =>
    intro k base jh hk hf hc hit
    have hklt : k < alive.length := by omega
    have hs := isColl_frame hf hs0
    obtain ⟨L1, hR1, hL1⟩ := gol_loop1_body (ip := ip) (hp := hp) base hs hc hit hklt h32 hc_ca hit_c hit_ca
    have hlt_c := Jvm.jvmHeap_get?_some_lt hc.1
    have hlt_it := Jvm.jvmHeap_get?_some_lt hit
    have hc' : IsColl (heap1 jh it sa ca k alive[k] (p1 alive k)) c LHS ca "java/lang/Object" (p1 alive (k + 1)) :=
      ⟨by rw [heap1_get_old hlt_c (Ne.symm hit_c) hc_ca]; exact hc.1,
        by rw [heap1_get_ca hc.2, p1_succ alive k hklt]⟩
    obtain ⟨L, jh', hR, hf', hc'', hit''⟩ := ih (k + 1) L1 _ (by omega) (heap1_frame hf hit0 hca0) hc'
      (heap1_get_it hit hit_ca)
    refine ⟨L, jh', ?_, hf', hc'', hit''⟩
    rw [show (rem + 1) * 21 + 3 = (rem * 21 + 3) + 21 by omega]
    refine reaches_trans hR1 ?_
    rw [hL1] at hR
    exact hR

/-- Locals at the head of the filter loop (pc 62). -/
def locs3 (base : Nat → JvmVal) (s r it : Nat) : Nat → JvmVal :=
  Jvm.setLocal (Jvm.setLocal (Jvm.setLocal base 0 (.heapRef s)) 3 (.heapRef r)) 5 (.heapRef it)

theorem locs3_self {L : Nat → JvmVal} {s r it : Nat} (h0 : L 0 = .heapRef s) (h3 : L 3 = .heapRef r)
    (h5 : L 5 = .heapRef it) : locs3 L s r it = L := by
  funext i
  simp only [locs3, Jvm.setLocal]
  repeat' split
  all_goals (subst_vars; first | rfl | (apply Eq.symm; assumption))

/-- The heap after the second phase (`candidates.addAll(aliveCells)`, result set, iterator). -/
def heap2 (jh : Jvm.JvmHeap AlgExt) (ca : Nat) (cand : List (Int32 × Int32)) : Jvm.JvmHeap AlgExt :=
  ((collHeap (jh.set ca (.objArray "java/lang/Object" (enc cand).toArray)) LHS (enc []).toArray).alloc
    (iterObj ca 0)).2

theorem gol_phase2 (L : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s sa c ca it : Nat} {scls sec : String}
    {alive acc : List (Int32 × Int32)}
    (hs : IsColl jh s scls sa sec alive) (hscls : scls = "java/util/Set" ∨ scls = LHS)
    (hc : IsColl jh c LHS ca "java/lang/Object" acc) (hc_ca : c ≠ ca) :
    ∃ L', Reaches HW P ⟨39, [], locs1 L s c it, jh, hp⟩
      ⟨62, [], locs3 L' s (jh.objects.size + 1) (jh.objects.size + 2),
        heap2 jh ca (alive.foldl ins acc), hp⟩ 23 := by
  have hsc : isAlgKotlinCollClass scls = true := by rcases hscls with rfl | rfl <;> rfl
  obtain ⟨b, hb⟩ := step_ifaceAddAll (ip := ip) (pc := 39 + 6) (stk := []) (hp := hp)
    (locs := Jvm.setLocal (locs1 L s c it) 1 (.heapRef c)) hs hsc hc hc_ca
  let jh2 := jh.set ca (.objArray "java/lang/Object" (enc (alive.foldl ins acc)).toArray)
  have hc2 : IsColl jh2 c LHS ca "java/lang/Object" (alive.foldl ins acc) :=
    ⟨by rw [Jvm.jvmHeap_get?_set_ne _ _ hc_ca]; exact hc.1, Jvm.jvmHeap_get?_set_self hc.2⟩
  have hc3 := isColl_frame (frame_collHeap jh2 LHS (enc []).toArray) hc2
  have hsz : jh2.objects.size = jh.objects.size := heap_set_size ..
  let L2 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (locs1 L s c it) 1 (.heapRef c)) 2
    (.heapRef c)) 3 (.heapRef (jh.objects.size + 1))) 4 (.i32 0)) 5 (.heapRef (jh.objects.size + 2))
  refine ⟨L2, ?_⟩
  rw [locs3_self (L := L2) rfl rfl rfl]
  gs
  gsh step_checkcast_inst hc.1 rfl
  gs; gs; gs
  gsh step_checkcast_inst hs.1 (setCls_sub scls hscls _ (.inr rfl))
  gsh hb
  gs; gs
  gsh step_checkcast_inst hc2.1 rfl
  gs; gs; gs
  gsh step_newLHS
  gsh step_checkcast_inst (collHeap_get_inst ..) rfl
  gsh step_checkcast_inst (collHeap_get_inst ..) rfl
  gs; gs; gs; gs; gs
  gsh step_iterator hc3 (.inr rfl)
  gs
  rw [collHeap_size, hsz]
  exact reaches_refl

/-- Locals at the head of the neighbor-count loop (pc 94). -/
def locs4 (base : Nat → JvmVal) (s r it2 : Nat) (cd : Int32 × Int32) (cnt : UInt32) (it3 : Nat) : Nat → JvmVal :=
  Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal base 0
    (.heapRef s)) 3 (.heapRef r)) 5 (.heapRef it2)) 6 (encV cd)) 7 (.i64 (pk cd))) 12 (.i32 cnt)) 13 (.heapRef it3)

theorem locs4_self {L : Nat → JvmVal} {s r it2 it3 : Nat} {cd : Int32 × Int32} {cnt : UInt32}
    (h0 : L 0 = .heapRef s) (h3 : L 3 = .heapRef r) (h5 : L 5 = .heapRef it2) (h6 : L 6 = encV cd)
    (h7 : L 7 = .i64 (pk cd)) (h12 : L 12 = .i32 cnt) (h13 : L 13 = .heapRef it3) :
    locs4 L s r it2 cd cnt it3 = L := by
  funext i
  simp only [locs4, Jvm.setLocal]
  repeat' split
  all_goals (subst_vars; first | rfl | (apply Eq.symm; assumption))

theorem sle0_ofNat {n : Nat} (hn : n < 2 ^ 31) : (0#32).sle (UInt32.ofNat n).toBitVec = true := by
  simp only [BitVec.sle, BitVec.toInt_zero]
  rw [Jvm.u32_toInt_eq_toNat (by rw [ofNat_toNat_of_lt (by omega)]; omega), ofNat_toNat_of_lt (by omega)]
  exact decide_eq_true (by omega)

/-- Neighbors among the first `k` of `nbs` that are alive. -/
def cntP (alive nbs : List (Int32 × Int32)) (k : Nat) : Nat :=
  ((nbs.take k).filter fun n => alive.contains n).length

theorem cntP_succ (alive nbs : List (Int32 × Int32)) (k : Nat) (hk : k < nbs.length) :
    cntP alive nbs (k + 1) = cntP alive nbs k + if alive.contains nbs[k] then 1 else 0 := by
  unfold cntP
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.filter_append, List.length_append]
  cases h : alive.contains nbs[k] <;>
    simp only [List.filter_cons, List.filter_nil, h, ↓reduceIte, Bool.false_eq_true, List.length_cons,
      List.length_nil]

theorem cntP_le (alive nbs : List (Int32 × Int32)) (k : Nat) : cntP alive nbs k ≤ k := by
  unfold cntP
  exact Nat.le_trans (List.length_filter_le _ _) (by simp only [List.length_take]; exact Nat.min_le_left _ _)

theorem gol_inner_body (base : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s sa r it2 it3 ma : Nat}
    {scls sec : String} {alive nbs : List (Int32 × Int32)} {cd : Int32 × Int32} {k c : Nat}
    (hs : IsColl jh s scls sa sec alive) (hsc : isAlgKotlinCollClass scls = true)
    (hma : jh.get? ma = some (.objArray "java/lang/Object" (enc nbs).toArray)) (hit3 : it3 < jh.objects.size)
    (hk : k < nbs.length) (h32 : nbs.length < 2 ^ 32) (hc : c + 1 < 2 ^ 31)
    (hs_it3 : s ≠ it3) (hsa_it3 : sa ≠ it3) (hma_it3 : ma ≠ it3) :
    ∃ L, Reaches HW P ⟨94, [], locs4 base s r it2 cd (UInt32.ofNat c) it3, jh.set it3 (iterObj ma (UInt32.ofNat k)), hp⟩
      ⟨94, [], L, jh.set it3 (iterObj ma (UInt32.ofNat (k + 1))), hp⟩ 20 ∧
      locs4 L s r it2 cd (UInt32.ofNat (c + if alive.contains nbs[k] then 1 else 0)) it3 = L := by
  have hlt := enc_size_lt hk h32
  have hitg : (jh.set it3 (iterObj ma (UInt32.ofNat k))).get? it3 = some (iterObj ma (UInt32.ofNat k)) :=
    heap_get_set_self_lt hit3
  have hmag : (jh.set it3 (iterObj ma (UInt32.ofNat k))).get? ma =
      some (.objArray "java/lang/Object" (enc nbs).toArray) := by
    rw [Jvm.jvmHeap_get?_set_ne _ _ hma_it3, hma]
  let jh2 := (jh.set it3 (iterObj ma (UInt32.ofNat k))).set it3 (iterObj ma (UInt32.ofNat k + 1))
  have hs2 : IsColl jh2 s scls sa sec alive :=
    ⟨by rw [Jvm.jvmHeap_get?_set_ne _ _ hs_it3, Jvm.jvmHeap_get?_set_ne _ _ hs_it3]; exact hs.1,
      by rw [Jvm.jvmHeap_get?_set_ne _ _ hsa_it3, Jvm.jvmHeap_get?_set_ne _ _ hsa_it3]; exact hs.2⟩
  have hjh2 : jh2 = jh.set it3 (iterObj ma (UInt32.ofNat (k + 1))) := by
    simp only [jh2, heap_set_set, ofNat_succ]
  let L1 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (locs4 base s r it2 cd (UInt32.ofNat c) it3) 14 (encV nbs[k]))
    15 (.i64 (pk nbs[k]))) 17 (.i32 0)
  cases hct : alive.contains nbs[k]
  · refine ⟨L1, ?_, locs4_self rfl rfl rfl rfl rfl (by simp [L1, Jvm.setLocal, locs4]) rfl⟩
    rw [← hjh2]
    gs
    gsh step_hasNext hitg hmag
    refine reaches_ifeq_fall defaultZero_hw rfl (hasNext_ne hk h32) ?_
    gs
    gsh step_next' hitg hmag hlt (enc_get hk h32 hlt)
    gs; gs; gs; gs; gs; gs; gs; gs; gs; gs
    gsh step_contains nbs[k] hs2 hsc
    refine reaches_ifeq_jump defaultZero_hw rfl (by rw [hct]; rfl) ?_
    exact reaches_refl
  · refine ⟨Jvm.setLocal L1 12 (.i32 (UInt32.ofNat c + (1 : Int32).toUInt32)), ?_,
      locs4_self rfl rfl rfl rfl rfl ?_ rfl⟩
    · rw [← hjh2]
      gs
      gsh step_hasNext hitg hmag
      refine reaches_ifeq_fall defaultZero_hw rfl (hasNext_ne hk h32) ?_
      gs
      gsh step_next' hitg hmag hlt (enc_get hk h32 hlt)
      gs; gs; gs; gs; gs; gs; gs; gs; gs; gs
      gsh step_contains nbs[k] hs2 hsc
      refine reaches_ifeq_fall defaultZero_hw rfl (by rw [hct]; decide) ?_
      gs; gs
      refine reaches_ifge_jump rfl (by
        rw [show (1 : Int32).toUInt32 = 1 from rfl, ofNat_succ]; exact sle0_ofNat hc) ?_
      exact reaches_refl
    · show JvmVal.i32 (UInt32.ofNat c + (1 : Int32).toUInt32) = _
      rw [show (1 : Int32).toUInt32 = 1 from rfl, ofNat_succ]
      simp

theorem gol_inner {jh : Jvm.JvmHeap AlgExt} {s sa r it2 it3 ma : Nat}
    {scls sec : String} {alive nbs : List (Int32 × Int32)} {cd : Int32 × Int32}
    (hs : IsColl jh s scls sa sec alive) (hsc : isAlgKotlinCollClass scls = true)
    (hma : jh.get? ma = some (.objArray "java/lang/Object" (enc nbs).toArray)) (hit3 : it3 < jh.objects.size)
    (h31 : nbs.length < 2 ^ 31) (hs_it3 : s ≠ it3) (hsa_it3 : sa ≠ it3) (hma_it3 : ma ≠ it3) :
    ∀ rem k base, k + rem = nbs.length →
      ∃ L, Reaches HW P
        ⟨94, [], locs4 base s r it2 cd (UInt32.ofNat (cntP alive nbs k)) it3,
          jh.set it3 (iterObj ma (UInt32.ofNat k)), hp⟩
        ⟨116, [], locs4 L s r it2 cd (UInt32.ofNat (cntP alive nbs nbs.length)) it3,
          jh.set it3 (iterObj ma (UInt32.ofNat nbs.length)), hp⟩ (rem * 20 + 3) := by
  intro rem
  induction rem with
  | zero =>
    intro k base hk
    have hk' : k = nbs.length := by omega
    subst hk'
    refine ⟨base, ?_⟩
    have hitg := heap_get_set_self_lt (w := iterObj ma (UInt32.ofNat nbs.length)) hit3
    have hmag : (jh.set it3 (iterObj ma (UInt32.ofNat nbs.length))).get? ma =
        some (.objArray "java/lang/Object" (enc nbs).toArray) := by
      rw [Jvm.jvmHeap_get?_set_ne _ _ hma_it3, hma]
    gs
    gsh step_hasNext hitg hmag
    refine reaches_ifeq_jump defaultZero_hw rfl (hasNext_eq (by omega)) ?_
    exact reaches_refl
  | succ rem ih =>
    intro k base hk
    have hklt : k < nbs.length := by omega
    have hc : cntP alive nbs k + 1 < 2 ^ 31 := by have := cntP_le alive nbs k; omega
    obtain ⟨L1, hR1, hL1⟩ := gol_inner_body (ip := ip) (hp := hp) (r := r) (it2 := it2) (cd := cd) base hs hsc hma
      hit3 hklt (by omega) hc hs_it3 hsa_it3 hma_it3
    obtain ⟨L, hR⟩ := ih (k + 1) L1 (by omega)
    refine ⟨L, ?_⟩
    rw [show (rem + 1) * 20 + 3 = (rem * 20 + 3) + 20 by omega]
    refine reaches_trans hR1 ?_
    rw [cntP_succ alive nbs k hklt, hL1] at hR
    exact hR

theorem ofNat_eq_iff {n m : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32) : UInt32.ofNat n = UInt32.ofNat m ↔ n = m := by
  constructor
  · intro h
    have := congrArg UInt32.toNat h
    rwa [ofNat_toNat_of_lt hn, ofNat_toNat_of_lt hm] at this
  · intro h; rw [h]

/-- The heap after the filter step for candidate `cd`: `cd` is added to the result when `keep`. -/
def addIf (keep : Bool) (jh : Jvm.JvmHeap AlgExt) (ra : Nat) (acc : List (Int32 × Int32)) (cd : Int32 × Int32) :
    Jvm.JvmHeap AlgExt :=
  if keep then jh.set ra (.objArray "java/lang/Object" (enc (ins acc cd)).toArray) else jh

theorem gol_post (L : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s sa r ra it2 it3 : Nat} {scls sec : String}
    {alive acc : List (Int32 × Int32)} {cd : Int32 × Int32} {n : Nat}
    (hs : IsColl jh s scls sa sec alive) (hsc : isAlgKotlinCollClass scls = true)
    (hr : IsColl jh r LHS ra "java/lang/Object" acc) (hr_ra : r ≠ ra) (hn : n ≤ 8) :
    ∃ L', Reaches HW P ⟨116, [], locs4 L s r it2 cd (UInt32.ofNat n) it3, jh, hp⟩
      ⟨62, [], L', addIf (n == 3 || (n == 2 && alive.contains cd)) jh ra acc cd, hp⟩ 22 ∧
      locs3 L' s r it2 = L' := by
  obtain ⟨b, hb⟩ := step_add (ip := ip) (pc := 116 + 19) (stk := []) (hp := hp)
    (locs := Jvm.setLocal (locs4 L s r it2 cd (UInt32.ofNat n) it3) 18 (.i32 (UInt32.ofNat n))) cd hr hr_ra
  let L1 := Jvm.setLocal (locs4 L s r it2 cd (UInt32.ofNat n) it3) 18 (.i32 (UInt32.ofNat n))
  refine ⟨L1, ?_, locs3_self rfl rfl rfl⟩
  by_cases h3 : n = 3
  · subst h3
    simp only [addIf, show ((3 : Nat) == 3 || ((3 : Nat) == 2 && alive.contains cd)) = true from rfl, ↓reduceIte]
    gs; gs; gs; gs
    refine reaches_if_icmpeq_jump rfl rfl ?_
    gs; gsg
    refine reaches_ifeq_fall defaultZero_hw rfl (by decide) ?_
    gs; gs
    gsh hb
    gs; gsg
    exact reaches_refl
  · have h3' : UInt32.ofNat n ≠ 3 := fun h => h3 ((ofNat_eq_iff (m := 3) (by omega) (by decide)).mp h)
    by_cases h2 : n = 2
    · subst h2
      cases hct : alive.contains cd
      · simp only [addIf, show ((2 : Nat) == 3 || ((2 : Nat) == 2 && false)) = false from rfl,
          Bool.false_eq_true, ↓reduceIte]
        gs; gs; gs; gs
        refine reaches_if_icmpeq_fall rfl h3' ?_
        gs; gs
        refine reaches_if_icmpne_fall rfl rfl ?_
        gs; gs; gs
        gsh step_contains cd hs hsc
        refine reaches_ifeq_jump defaultZero_hw rfl (by rw [hct]; rfl) ?_
        gs
        refine reaches_ifeq_jump defaultZero_hw rfl rfl ?_
        exact reaches_refl
      · simp only [addIf, show ((2 : Nat) == 3 || ((2 : Nat) == 2 && true)) = true from rfl, ↓reduceIte]
        gs; gs; gs; gs
        refine reaches_if_icmpeq_fall rfl h3' ?_
        gs; gs
        refine reaches_if_icmpne_fall rfl rfl ?_
        gs; gs; gs
        gsh step_contains cd hs hsc
        refine reaches_ifeq_fall defaultZero_hw rfl (by rw [hct]; decide) ?_
        gs; gsg
        refine reaches_ifeq_fall defaultZero_hw rfl (by decide) ?_
        gs; gs
        gsh hb
        gs; gsg
        exact reaches_refl
    · have h2' : UInt32.ofNat n ≠ 2 := fun h => h2 ((ofNat_eq_iff (m := 2) (by omega) (by decide)).mp h)
      have hk : (n == 3 || (n == 2 && alive.contains cd)) = false := by simp [h3, h2]
      simp only [addIf, hk, Bool.false_eq_true, ↓reduceIte]
      gs; gs; gs; gs
      refine reaches_if_icmpeq_fall rfl h3' ?_
      gs; gs
      refine reaches_if_icmpne_jump rfl h2' ?_
      gs
      refine reaches_ifeq_jump defaultZero_hw rfl rfl ?_
      exact reaches_refl

theorem heap_get_alloc_new (h : Jvm.JvmHeap AlgExt) (o : Jvm.HeapObj AlgExt) :
    (h.alloc o).2.get? h.objects.size = some o := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]

/-- The heap at the head of the neighbor-count loop for candidate `cd` (the `k`-th, iterated by `it2` over `ca`):
the filter iterator advanced, `cd.getMooreNeighbors()` allocated, and its iterator allocated. -/
def candHeap (jh : Jvm.JvmHeap AlgExt) (it2 ca k : Nat) (cd : Int32 × Int32) : Jvm.JvmHeap AlgExt :=
  ((collHeap (jh.set it2 (iterObj ca (UInt32.ofNat k + 1))) LHS (enc (mooreNeighbors32 cd)).toArray).alloc
    (iterObj jh.objects.size 0)).2

theorem candHeap_size (jh : Jvm.JvmHeap AlgExt) (it2 ca k : Nat) (cd : Int32 × Int32) :
    (candHeap jh it2 ca k cd).objects.size = jh.objects.size + 3 := by
  simp only [candHeap, heap_alloc_size, collHeap_size, heap_set_size]

theorem candHeap_get_old {jh : Jvm.JvmHeap AlgExt} {it2 ca k x : Nat} {cd : Int32 × Int32}
    (hx : x < jh.objects.size) (hxit : x ≠ it2) : (candHeap jh it2 ca k cd).get? x = jh.get? x := by
  unfold candHeap
  rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [collHeap_size, heap_set_size]; omega),
    collHeap_get_old _ _ _ (by rw [heap_set_size]; exact hx), Jvm.jvmHeap_get?_set_ne _ _ hxit]

theorem candHeap_get_it2 {jh : Jvm.JvmHeap AlgExt} {it2 ca k : Nat} {cd : Int32 × Int32}
    (hit : jh.get? it2 = some (iterObj ca (UInt32.ofNat k))) :
    (candHeap jh it2 ca k cd).get? it2 = some (iterObj ca (UInt32.ofNat (k + 1))) := by
  have hlt := Jvm.jvmHeap_get?_some_lt hit
  unfold candHeap
  rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [collHeap_size, heap_set_size]; omega),
    collHeap_get_old _ _ _ (by rw [heap_set_size]; exact hlt), Jvm.jvmHeap_get?_set_self hit, ofNat_succ]

theorem candHeap_get_ma (jh : Jvm.JvmHeap AlgExt) (it2 ca k : Nat) (cd : Int32 × Int32) :
    (candHeap jh it2 ca k cd).get? jh.objects.size =
      some (.objArray "java/lang/Object" (enc (mooreNeighbors32 cd)).toArray) := by
  unfold candHeap
  rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [collHeap_size, heap_set_size]; omega)]
  have := collHeap_get_arr (jh.set it2 (iterObj ca (UInt32.ofNat k + 1))) LHS (enc (mooreNeighbors32 cd)).toArray
  rwa [heap_set_size] at this

theorem candHeap_get_it3 (jh : Jvm.JvmHeap AlgExt) (it2 ca k : Nat) (cd : Int32 × Int32) :
    (candHeap jh it2 ca k cd).get? (jh.objects.size + 2) = some (iterObj jh.objects.size 0) := by
  unfold candHeap
  have := heap_get_alloc_new (collHeap (jh.set it2 (iterObj ca (UInt32.ofNat k + 1))) LHS
    (enc (mooreNeighbors32 cd)).toArray) (iterObj jh.objects.size 0)
  rwa [collHeap_size, heap_set_size] at this

theorem moore_isEmpty (c : Int32 × Int32) :
    (if (mooreNeighbors32 c).isEmpty then (1 : UInt32) else 0) = 0 := rfl

theorem moore_length (c : Int32 × Int32) : (mooreNeighbors32 c).length = 8 := rfl

/-- From the filter loop head (pc 62) to the neighbor-count loop head (pc 94) for the `k`-th candidate. -/
theorem gol_cand_head (base : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s r it2 ca : Nat}
    {cand : List (Int32 × Int32)} {k : Nat}
    (hit : jh.get? it2 = some (iterObj ca (UInt32.ofNat k)))
    (hca : jh.get? ca = some (.objArray "java/lang/Object" (enc cand).toArray))
    (hk : k < cand.length) (h32 : cand.length < 2 ^ 32) :
    ∃ L, Reaches HW P ⟨62, [], locs3 base s r it2, jh, hp⟩
      ⟨94, [], L, (candHeap jh it2 ca k cand[k]).set (jh.objects.size + 2)
        (iterObj jh.objects.size (UInt32.ofNat 0)), hp⟩ 30 ∧
      locs4 L s r it2 cand[k] (UInt32.ofNat 0) (jh.objects.size + 2) = L := by
  have hlt := enc_size_lt hk h32
  have hsz : (jh.set it2 (iterObj ca (UInt32.ofNat k + 1))).objects.size = jh.objects.size := heap_set_size ..
  let jh1 := jh.set it2 (iterObj ca (UInt32.ofNat k + 1))
  have hm := isColl_collHeap jh1 LHS (mooreNeighbors32 cand[k])
  let L0 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (locs3 base s r it2) 6 (encV cand[k])) 7
    (.i64 (pk cand[k]))) 9 (.i32 0)) 10 (.heapRef (jh.objects.size + 1))
  refine ⟨Jvm.setLocal (Jvm.setLocal (Jvm.setLocal L0 11 (.i32 0)) 12 (.i32 0)) 13
    (.heapRef (jh.objects.size + 2)), ?_, locs4_self rfl rfl rfl rfl rfl rfl rfl⟩
  rw [show UInt32.ofNat 0 = 0 from rfl, heap_set_get_self (candHeap_get_it3 jh it2 ca k cand[k])]
  gs
  gsh step_hasNext hit hca
  refine reaches_ifeq_fall defaultZero_hw rfl (hasNext_ne hk h32) ?_
  gs
  gsh step_next' hit hca hlt (enc_get hk h32 hlt)
  gs; gs; gs; gs; gs; gs; gs; gs
  gsh step_moore cand[k]
  gsh step_checkcast_inst (collHeap_get_inst ..) rfl
  gs; gs; gs; gs
  gsh step_instanceof_inst (collHeap_get_inst ..) rfl
  refine reaches_ifeq_fall defaultZero_hw rfl (by decide) ?_
  gs
  gsh step_checkcast_inst (collHeap_get_inst ..) rfl
  gsh step_isEmpty hm rfl
  refine reaches_ifeq_jump defaultZero_hw rfl (moore_isEmpty _) ?_
  gs; gs; gs
  gsh step_iterator hm (.inr rfl)
  gs
  rw [collHeap_size, hsz]
  exact reaches_refl

/-- `stepGeneration`'s filter predicate for candidate `cd`, from the neighbor count of the bytecode's loop. -/
def keepF (alive : List (Int32 × Int32)) (cd : Int32 × Int32) : Bool :=
  cntP alive (mooreNeighbors32 cd) 8 == 3 || (cntP alive (mooreNeighbors32 cd) 8 == 2 && alive.contains cd)

/-- The heap after one iteration of the filter loop on the `k`-th candidate `cd`. -/
def loop2Heap (jh : Jvm.JvmHeap AlgExt) (it2 ca ra k : Nat) (alive acc : List (Int32 × Int32))
    (cd : Int32 × Int32) : Jvm.JvmHeap AlgExt :=
  addIf (keepF alive cd) ((candHeap jh it2 ca k cd).set (jh.objects.size + 2)
    (iterObj jh.objects.size (UInt32.ofNat 8))) ra acc cd

theorem isColl_candHeap {jh : Jvm.JvmHeap AlgExt} {it2 ca k a arr : Nat} {cd : Int32 × Int32} {cls ec : String}
    {l : List (Int32 × Int32)} (hc : IsColl jh a cls arr ec l) (ha : a ≠ it2) (harr : arr ≠ it2)
    (v : Jvm.HeapObj AlgExt) :
    IsColl ((candHeap jh it2 ca k cd).set (jh.objects.size + 2) v) a cls arr ec l := by
  have h1 := Jvm.jvmHeap_get?_some_lt hc.1
  have h2 := Jvm.jvmHeap_get?_some_lt hc.2
  exact ⟨by rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega), candHeap_get_old h1 ha]; exact hc.1,
    by rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega), candHeap_get_old h2 harr]; exact hc.2⟩

/-- One iteration of the filter loop (pc 62 back to pc 62). -/
theorem gol_loop2_body (base : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s sa r ra it2 ca : Nat}
    {scls sec : String} {alive cand acc : List (Int32 × Int32)} {k : Nat}
    (hs : IsColl jh s scls sa sec alive) (hsc : isAlgKotlinCollClass scls = true)
    (hr : IsColl jh r LHS ra "java/lang/Object" acc) (hr_ra : r ≠ ra)
    (hit : jh.get? it2 = some (iterObj ca (UInt32.ofNat k)))
    (hca : jh.get? ca = some (.objArray "java/lang/Object" (enc cand).toArray))
    (hk : k < cand.length) (h32 : cand.length < 2 ^ 32)
    (hs_it2 : s ≠ it2) (hsa_it2 : sa ≠ it2) (hr_it2 : r ≠ it2) (hra_it2 : ra ≠ it2) :
    ∃ L, Reaches HW P ⟨62, [], locs3 base s r it2, jh, hp⟩
      ⟨62, [], L, loop2Heap jh it2 ca ra k alive acc cand[k], hp⟩ 215 ∧ locs3 L s r it2 = L := by
  obtain ⟨L1, hR1, hL1⟩ := gol_cand_head (ip := ip) (hp := hp) base (s := s) (r := r) hit hca hk h32
  have hsl := Jvm.jvmHeap_get?_some_lt hs.1
  have hsal := Jvm.jvmHeap_get?_some_lt hs.2
  have hs3 : IsColl (candHeap jh it2 ca k cand[k]) s scls sa sec alive :=
    ⟨by rw [candHeap_get_old hsl hs_it2]; exact hs.1, by rw [candHeap_get_old hsal hsa_it2]; exact hs.2⟩
  obtain ⟨L2, hR2⟩ := gol_inner (ip := ip) (hp := hp) (r := r) (it2 := it2) (cd := cand[k]) (it3 := jh.objects.size + 2)
    (ma := jh.objects.size) hs3 hsc
    (candHeap_get_ma jh it2 ca k cand[k]) (by rw [candHeap_size]; omega) (by rw [moore_length]; decide)
    (by omega) (by omega) (by omega) 8 0 L1 (by rw [moore_length])
  rw [moore_length] at hR2
  have hs4 := isColl_candHeap (ca := ca) (k := k) (cd := cand[k]) hs hs_it2 hsa_it2
    (iterObj jh.objects.size (UInt32.ofNat 8))
  have hr4 := isColl_candHeap (ca := ca) (k := k) (cd := cand[k]) hr hr_it2 hra_it2
    (iterObj jh.objects.size (UInt32.ofNat 8))
  obtain ⟨L3, hR3, hL3⟩ := gol_post (ip := ip) (hp := hp) L2 (it3 := jh.objects.size + 2) (cd := cand[k])
    hs4 hsc hr4 hr_ra (cntP_le alive (mooreNeighbors32 cand[k]) 8)
  refine ⟨L3, ?_, hL3⟩
  rw [← hL1] at hR1
  exact reaches_mono (reaches_trans (reaches_trans hR1 hR2) hR3) (by omega)

/-- One filter step on the result set: add `cd` when it is kept. -/
def stepF (alive acc : List (Int32 × Int32)) (cd : Int32 × Int32) : List (Int32 × Int32) :=
  if keepF alive cd then ins acc cd else acc

/-- The result set after the filter loop's first `k` iterations. -/
def p2 (alive cand : List (Int32 × Int32)) (k : Nat) : List (Int32 × Int32) :=
  (cand.take k).foldl (stepF alive) []

theorem p2_succ (alive cand : List (Int32 × Int32)) (k : Nat) (hk : k < cand.length) :
    p2 alive cand (k + 1) = stepF alive (p2 alive cand k) cand[k] := by
  unfold p2
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem addIf_size (keep : Bool) (jh : Jvm.JvmHeap AlgExt) (ra : Nat) (acc : List (Int32 × Int32))
    (cd : Int32 × Int32) : (addIf keep jh ra acc cd).objects.size = jh.objects.size := by
  unfold addIf; split
  · exact heap_set_size ..
  · rfl

theorem addIf_get_ne {keep : Bool} {jh : Jvm.JvmHeap AlgExt} {ra x : Nat} {acc : List (Int32 × Int32)}
    {cd : Int32 × Int32} (hx : x ≠ ra) : (addIf keep jh ra acc cd).get? x = jh.get? x := by
  unfold addIf; split
  · exact Jvm.jvmHeap_get?_set_ne _ _ hx
  · rfl

theorem loop2Heap_size (jh : Jvm.JvmHeap AlgExt) (it2 ca ra k : Nat) (alive acc : List (Int32 × Int32))
    (cd : Int32 × Int32) : (loop2Heap jh it2 ca ra k alive acc cd).objects.size = jh.objects.size + 3 := by
  simp only [loop2Heap, addIf_size, heap_set_size, candHeap_size]

theorem loop2Heap_get_old {jh : Jvm.JvmHeap AlgExt} {it2 ca ra k x : Nat} {alive acc : List (Int32 × Int32)}
    {cd : Int32 × Int32} (hx : x < jh.objects.size) (hxit : x ≠ it2) (hxra : x ≠ ra) :
    (loop2Heap jh it2 ca ra k alive acc cd).get? x = jh.get? x := by
  simp only [loop2Heap]
  rw [addIf_get_ne hxra, Jvm.jvmHeap_get?_set_ne _ _ (by omega), candHeap_get_old hx hxit]

theorem loop2Heap_get_it2 {jh : Jvm.JvmHeap AlgExt} {it2 ca ra k : Nat} {alive acc : List (Int32 × Int32)}
    {cd : Int32 × Int32} (hit : jh.get? it2 = some (iterObj ca (UInt32.ofNat k))) (hra : ra ≠ it2) :
    (loop2Heap jh it2 ca ra k alive acc cd).get? it2 = some (iterObj ca (UInt32.ofNat (k + 1))) := by
  have hlt := Jvm.jvmHeap_get?_some_lt hit
  simp only [loop2Heap]
  rw [addIf_get_ne (Ne.symm hra), Jvm.jvmHeap_get?_set_ne _ _ (by omega), candHeap_get_it2 hit]

theorem loop2Heap_get_ra {jh : Jvm.JvmHeap AlgExt} {it2 ca ra k : Nat} {alive acc : List (Int32 × Int32)}
    {cd : Int32 × Int32} (hra : jh.get? ra = some (.objArray "java/lang/Object" (enc acc).toArray))
    (hra_it2 : ra ≠ it2) :
    (loop2Heap jh it2 ca ra k alive acc cd).get? ra =
      some (.objArray "java/lang/Object" (enc (stepF alive acc cd)).toArray) := by
  have hlt := Jvm.jvmHeap_get?_some_lt hra
  have hold : ((candHeap jh it2 ca k cd).set (jh.objects.size + 2)
      (iterObj jh.objects.size (UInt32.ofNat 8))).get? ra = jh.get? ra := by
    rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega), candHeap_get_old hlt hra_it2]
  simp only [loop2Heap, addIf, stepF]
  split
  · apply heap_get_set_self_lt
    rw [heap_set_size, candHeap_size]; omega
  · rw [hold, hra]

theorem gol_loop2 {jhIn : Jvm.JvmHeap AlgExt} {s sa r ra it2 ca : Nat} {scls sec : String}
    {alive cand : List (Int32 × Int32)}
    (hs0 : IsColl jhIn s scls sa sec alive) (hsc : isAlgKotlinCollClass scls = true) (h32 : cand.length < 2 ^ 32)
    (hr_ra : r ≠ ra) (hr_it2 : r ≠ it2) (hra_it2 : ra ≠ it2) (hca_it2 : ca ≠ it2) (hca_ra : ca ≠ ra)
    (hra_in : jhIn.objects.size ≤ ra) (hit_in : jhIn.objects.size ≤ it2) :
    ∀ rem k base jh, k + rem = cand.length → Frame jhIn jh →
      jh.get? r = some (.instance LHS [("arr", .heapRef ra)]) →
      jh.get? ra = some (.objArray "java/lang/Object" (enc (p2 alive cand k)).toArray) →
      jh.get? it2 = some (iterObj ca (UInt32.ofNat k)) →
      jh.get? ca = some (.objArray "java/lang/Object" (enc cand).toArray) →
      ∃ L jh', Reaches HW P ⟨62, [], locs3 base s r it2, jh, hp⟩ ⟨140, [.heapRef r], L, jh', hp⟩ (rem * 215 + 5) ∧
        Frame jhIn jh' ∧ IsColl jh' r LHS ra "java/lang/Object" (p2 alive cand cand.length) := by
  have hs_in := Jvm.jvmHeap_get?_some_lt hs0.1
  have hsa_in := Jvm.jvmHeap_get?_some_lt hs0.2
  intro rem
  induction rem with
  | zero =>
    intro k base jh hk hf hr hra hit hca
    have hk' : k = cand.length := by omega
    subst hk'
    refine ⟨locs3 base s r it2, jh, ?_, hf, hr, hra⟩
    gs
    gsh step_hasNext hit hca
    refine reaches_ifeq_jump defaultZero_hw rfl (hasNext_eq h32) ?_
    gs
    gsh step_checkcast_inst hr rfl
    exact reaches_refl
  | succ rem ih =>
    intro k base jh hk hf hr hra hit hca
    have hklt : k < cand.length := by omega
    have hs := isColl_frame hf hs0
    obtain ⟨L1, hR1, hL1⟩ := gol_loop2_body (ip := ip) (hp := hp) base hs hsc ⟨hr, hra⟩ hr_ra hit hca hklt h32
      (by omega) (by omega) hr_it2 hra_it2
    have hrl := Jvm.jvmHeap_get?_some_lt hr
    have hcal := Jvm.jvmHeap_get?_some_lt hca
    have hf' : Frame jhIn (loop2Heap jh it2 ca ra k alive (p2 alive cand k) cand[k]) :=
      ⟨by rw [loop2Heap_size]; have := hf.1; omega, fun x hx => by
        rw [loop2Heap_get_old (by have := hf.1; omega) (by omega) (by omega), hf.2 x hx]⟩
    obtain ⟨L, jh', hR, hf'', hc''⟩ := ih (k + 1) L1 _ (by omega) hf'
      (by rw [loop2Heap_get_old hrl hr_it2 hr_ra]; exact hr)
      (by rw [loop2Heap_get_ra hra hra_it2, p2_succ alive cand k hklt])
      (loop2Heap_get_it2 hit hra_it2)
      (by rw [loop2Heap_get_old hcal hca_it2 hca_ra]; exact hca)
    refine ⟨L, jh', ?_, hf'', hc''⟩
    rw [show (rem + 1) * 215 + 5 = (rem * 215 + 5) + 215 by omega]
    refine reaches_trans hR1 ?_
    rw [hL1] at hR
    exact hR

/-- `GameOfLifeStepKt_stepGeneration_prog` from entry to its `areturn` (pc 140). -/
theorem gol_reaches (base : Nat → JvmVal) {jh : Jvm.JvmHeap AlgExt} {s sa : Nat} {scls sec : String}
    {alive : List (Int32 × Int32)}
    (hs : IsColl jh s scls sa sec alive) (hscls : scls = "java/util/Set" ∨ scls = LHS)
    (h32 : alive.length < 2 ^ 32)
    (hc32 : (alive.foldl ins (p1 alive alive.length)).length < 2 ^ 32) :
    ∃ L jh' r ra, Reaches HW P ⟨0, [], Jvm.setLocal base 0 (.heapRef s), jh, hp⟩ ⟨140, [.heapRef r], L, jh', hp⟩
        ((alive.foldl ins (p1 alive alive.length)).length * 215 + 5 + 23 + (alive.length * 21 + 3) + 18) ∧
      Frame jh jh' ∧
      IsColl jh' r LHS ra "java/lang/Object"
        (p2 alive (alive.foldl ins (p1 alive alive.length)) (alive.foldl ins (p1 alive alive.length)).length) := by
  have hsc : isAlgKotlinCollClass scls = true := by rcases hscls with rfl | rfl <;> rfl
  have hR0 := gol_prologue (ip := ip) (hp := hp) base hs hscls
  let H1 := ((collHeap jh LHS (enc []).toArray).alloc (iterObj sa 0)).2
  have hfH1 : Frame jh H1 := frame_trans (frame_collHeap ..) (frame_alloc ..)
  have hcH1 : IsColl H1 (jh.objects.size + 1) LHS jh.objects.size "java/lang/Object" (p1 alive 0) :=
    isColl_frame (frame_alloc ..) (isColl_collHeap jh LHS [])
  have hitH1 : H1.get? (jh.objects.size + 2) = some (iterObj sa (UInt32.ofNat 0)) := by
    have := heap_get_alloc_new (collHeap jh LHS (enc []).toArray) (iterObj sa 0)
    rw [collHeap_size] at this
    exact this
  obtain ⟨L1, jh1, hR1, hf1, hc1, -⟩ := gol_loop1 (ip := ip) (hp := hp) hs h32 (by omega) (by omega) (by omega)
    (Nat.le_refl _) (by omega) alive.length 0 base H1 (by omega) hfH1 hcH1 hitH1
  obtain ⟨L2, hR2⟩ := gol_phase2 (ip := ip) (hp := hp) (it := jh.objects.size + 2) L1 (isColl_frame hf1 hs) hscls
    hc1 (by omega)
  -- the heap after phase 2
  let cand := alive.foldl ins (p1 alive alive.length)
  let jh2 := jh1.set jh.objects.size (.objArray "java/lang/Object" (enc cand).toArray)
  have hca1 := Jvm.jvmHeap_get?_some_lt hc1.2
  have hsz2 : jh2.objects.size = jh1.objects.size := heap_set_size ..
  have hf2 : Frame jh (heap2 jh1 jh.objects.size cand) :=
    frame_trans (frame_collHeap ..) (frame_alloc ..) |> frame_trans (frame_set _ hf1 (Nat.le_refl _))
  have hr2 : (heap2 jh1 jh.objects.size cand).get? (jh1.objects.size + 1) =
      some (.instance LHS [("arr", .heapRef jh1.objects.size)]) := by
    simp only [heap2]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [collHeap_size, heap_set_size]; omega)]
    have := collHeap_get_inst jh2 LHS (enc []).toArray
    rwa [hsz2] at this
  have hra2 : (heap2 jh1 jh.objects.size cand).get? jh1.objects.size =
      some (.objArray "java/lang/Object" (enc (p2 alive cand 0)).toArray) := by
    simp only [heap2]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [collHeap_size, heap_set_size]; omega)]
    have := collHeap_get_arr jh2 LHS (enc []).toArray
    rwa [hsz2] at this
  have hit2 : (heap2 jh1 jh.objects.size cand).get? (jh1.objects.size + 2) =
      some (iterObj jh.objects.size (UInt32.ofNat 0)) := by
    simp only [heap2]
    have := heap_get_alloc_new (collHeap jh2 LHS (enc []).toArray) (iterObj jh.objects.size 0)
    rwa [collHeap_size, hsz2] at this
  have hcand2 : (heap2 jh1 jh.objects.size cand).get? jh.objects.size =
      some (.objArray "java/lang/Object" (enc cand).toArray) := by
    simp only [heap2]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [collHeap_size, hsz2]; omega),
      collHeap_get_old _ _ _ (by rw [hsz2]; omega)]
    exact Jvm.jvmHeap_get?_set_self hc1.2
  have hjh1 := hf1.1
  obtain ⟨L3, jh3, hR3, hf3, hc3⟩ := gol_loop2 (ip := ip) (hp := hp) (cand := cand) (it2 := jh1.objects.size + 2)
    (r := jh1.objects.size + 1) (ra := jh1.objects.size) (ca := jh.objects.size) hs hsc hc32
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    cand.length 0 L2 _ (by omega) hf2 hr2 hra2 hit2 hcand2
  refine ⟨L3, jh3, jh1.objects.size + 1, jh1.objects.size, ?_, hf3, hc3⟩
  exact reaches_mono (reaches_trans (reaches_trans (reaches_trans hR0 hR1) hR2) hR3) (by simp only [cand]; omega)

end StepGeneration

/-! ## From the bytecode's sets to `stepGenerationModel` -/

theorem dedupCoords_eq (xs : List (Int32 × Int32)) : dedupCoords xs = xs.foldl ins [] := rfl

theorem foldl_ins_of_nodup : ∀ (acc l : List (Int32 × Int32)), (acc ++ l).Nodup → l.foldl ins acc = acc ++ l
  | acc, [], _ => by simp
  | acc, x :: l, hnd => by
    have hx : x ∉ acc := by
      intro hm
      exact (List.nodup_append.mp hnd).2.2 x hm x (List.mem_cons_self ..) rfl
    have hins : ins acc x = acc ++ [x] := by simp [ins, hx]
    rw [List.foldl_cons, hins, foldl_ins_of_nodup (acc ++ [x]) l (by simpa using hnd)]
    simp

theorem ins_nodup {acc : List (Int32 × Int32)} (x : Int32 × Int32) (h : acc.Nodup) : (ins acc x).Nodup := by
  unfold ins
  split
  · exact h
  · rename_i hx
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hb; subst hab
    exact hx (by simpa using ha)

theorem foldl_ins_nodup : ∀ (l acc : List (Int32 × Int32)), acc.Nodup → (l.foldl ins acc).Nodup
  | [], _, h => h
  | x :: l, acc, h => foldl_ins_nodup l (ins acc x) (ins_nodup x h)

theorem foldl_ins_length : ∀ (l acc : List (Int32 × Int32)), (l.foldl ins acc).length ≤ acc.length + l.length
  | [], acc => by simp
  | x :: l, acc => by
    have h1 : (ins acc x).length ≤ acc.length + 1 := by
      unfold ins; split <;> simp
    have := foldl_ins_length l (ins acc x)
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem flatMap_moore_length : ∀ (l : List (Int32 × Int32)), (l.flatMap mooreNeighbors32).length = 8 * l.length
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, moore_length, flatMap_moore_length l, List.length_cons]
    omega

theorem foldl_stepF (alive : List (Int32 × Int32)) :
    ∀ (l acc : List (Int32 × Int32)), l.Nodup → (∀ x ∈ l, x ∉ acc) →
      l.foldl (stepF alive) acc = acc ++ l.filter (keepF alive)
  | [], acc, _, _ => by simp
  | x :: l, acc, hnd, hdisj => by
    have hnd' := List.nodup_cons.mp hnd
    rw [List.foldl_cons, List.filter_cons]
    cases hk : keepF alive x
    · have hs : stepF alive acc x = acc := by simp [stepF, hk]
      simp only [hs, Bool.false_eq_true, ↓reduceIte]
      exact foldl_stepF alive l acc hnd'.2 (fun y hy => hdisj y (List.mem_cons_of_mem _ hy))
    · have hs : stepF alive acc x = acc ++ [x] := by
        simp [stepF, hk, ins, hdisj x (List.mem_cons_self ..)]
      simp only [hs, ↓reduceIte]
      rw [foldl_stepF alive l (acc ++ [x]) hnd'.2 (fun y hy hm => by
        rcases List.mem_append.mp hm with hm | hm
        · exact hdisj y (List.mem_cons_of_mem _ hy) hm
        · rw [List.mem_singleton] at hm; subst hm; exact hnd'.1 hy)]
      simp

theorem keepF_eq (alive : List (Int32 × Int32)) (c : Int32 × Int32) :
    keepF alive c =
      ((((mooreNeighbors32 c).filter fun n => alive.contains n).length == 3) ||
        ((((mooreNeighbors32 c).filter fun n => alive.contains n).length == 2) && alive.contains c)) := by
  unfold keepF cntP
  rw [List.take_of_length_le (Nat.le_of_eq (moore_length c))]

/-- The candidate list of the bytecode (first loop, then `addAll(aliveCells)`). -/
def candOf (alive : List (Int32 × Int32)) : List (Int32 × Int32) := alive.foldl ins (p1 alive alive.length)

theorem candOf_eq (alive : List (Int32 × Int32)) :
    candOf alive = (alive.flatMap mooreNeighbors32 ++ alive).foldl ins [] := by
  unfold candOf p1
  rw [List.take_length, List.foldl_append]

theorem candOf_length (alive : List (Int32 × Int32)) : (candOf alive).length ≤ 9 * alive.length := by
  rw [candOf_eq]
  have := foldl_ins_length (alive.flatMap mooreNeighbors32 ++ alive) []
  rw [List.length_append, flatMap_moore_length] at this
  simp only [List.length_nil] at this
  omega

theorem p2_candOf (alive : List (Int32 × Int32)) (hnd : alive.Nodup) :
    p2 alive (candOf alive) (candOf alive).length = stepGenerationModel alive := by
  have hcnd : (candOf alive).Nodup := by
    rw [candOf_eq]; exact foldl_ins_nodup _ [] List.nodup_nil
  unfold p2
  rw [List.take_length, foldl_stepF alive _ [] hcnd (fun _ _ h => by cases h), List.nil_append]
  have ha : dedupCoords alive = alive := by
    rw [dedupCoords_eq, foldl_ins_of_nodup [] alive (by simpa using hnd), List.nil_append]
  unfold stepGenerationModel
  simp only [ha]
  rw [dedupCoords_eq, ← candOf_eq]
  exact List.filter_congr (fun c _ => keepF_eq alive c)

theorem stepGenerationModel_nodup (alive : List (Int32 × Int32)) : (stepGenerationModel alive).Nodup := by
  unfold stepGenerationModel
  simp only [dedupCoords_eq]
  exact (foldl_ins_nodup _ [] List.nodup_nil).filter _

/-- `GameOfLifeStepKt_stepGeneration_prog` under `algKotlinHooksWith ip` (it makes no calls into lifted classes). -/
theorem stepGeneration_run {ip : String → JvmState → List (Nat × JvmVal) → Option (Option (JvmVal × JvmState))}
    (base : Nat → JvmVal) (fuel : Nat) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {s sa : Nat} {scls sec : String}
    {alive : List (Int32 × Int32)}
    (hs : IsColl jh s scls sa sec alive) (hscls : scls = "java/util/Set" ∨ scls = "java/util/LinkedHashSet")
    (hnd : alive.Nodup) (h9 : 9 * alive.length < 2 ^ 32) (hf : 2000 * (alive.length + 1) ≤ fuel) :
    ∃ r ra endSt, Jvm.runJvmRes (algKotlinHooksWith ip) fuel GameOfLifeStepKt_stepGeneration_prog
        ⟨0, [], Jvm.setLocal base 0 (.heapRef s), jh, hp⟩ = some (.heapRef r, endSt) ∧
      IsColl endSt.jvmHeap r "java/util/LinkedHashSet" ra "java/lang/Object" (stepGenerationModel alive) ∧
      Frame jh endSt.jvmHeap ∧ endSt.heap = hp := by
  have hcl := candOf_length alive
  obtain ⟨L, jh', r, ra, hR, hf', hc⟩ := gol_reaches (ip := ip) (hp := hp) base hs hscls (by omega)
    (show (candOf alive).length < 2 ^ 32 by omega)
  rw [show alive.foldl ins (p1 alive alive.length) = candOf alive from rfl, p2_candOf alive hnd] at hc
  rw [show alive.foldl ins (p1 alive alive.length) = candOf alive from rfl] at hR
  refine ⟨r, ra, _, run_of_reaches_ret hR rfl rfl (by omega), hc, hf', rfl⟩

/-! ## `stepGenerations` -/

/-- The `resolveProg` tag of `stepGeneration`. -/
abbrev stepGenerationTag : String := "GameOfLifeStepKt.stepGeneration:(Ljava/util/Set;)Ljava/util/Set;"

theorem algKotlinProgLookup_stepGeneration : algKotlinProgLookup stepGenerationTag = some GameOfLifeStepKt_stepGeneration_prog := by
  simp [algKotlinProgLookup, stepGenerationTag]

/-- `invokestatic stepGeneration` under `mkAlgKotlinHooks` runs `GameOfLifeStepKt_stepGeneration_prog` with the argument in slot 0. -/
theorem step_call_gen {rp : String → Option (List JvmInstr)} {d sf pc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cur : Nat} {res : JvmVal} {endSt : JvmState}
    (hr : rp stepGenerationTag = some GameOfLifeStepKt_stepGeneration_prog)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf GameOfLifeStepKt_stepGeneration_prog
      ⟨0, [], Jvm.setLocal (fun _ => .i32 0) 0 (.heapRef cur), jh, hp⟩ = some (res, endSt)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf)
        (.invokestatic "com/alexvanyo/composelife/algorithm/GameOfLifeStepKt" "stepGeneration" "(Ljava/util/Set;)Ljava/util/Set;")
        ⟨pc, .heapRef cur :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩) := by
  have hgen : ∀ st, Jvm.stepInvokeStaticGeneric (mkAlgKotlinHooks rp (d + 1) sf) st "GameOfLifeStepKt"
      "stepGeneration" "(Ljava/util/Set;)Ljava/util/Set;" = (mkAlgKotlinHooks rp (d + 1) sf).stepInvokeStatic st
      "GameOfLifeStepKt" "stepGeneration" "(Ljava/util/Set;)Ljava/util/Set;" := fun _ => rfl
  have hstep : ∀ st, Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf)
      (.invokestatic "com/alexvanyo/composelife/algorithm/GameOfLifeStepKt" "stepGeneration" "(Ljava/util/Set;)Ljava/util/Set;") st =
      Jvm.stepInvokeStaticGeneric (mkAlgKotlinHooks rp (d + 1) sf) st "GameOfLifeStepKt"
      "stepGeneration" "(Ljava/util/Set;)Ljava/util/Set;" := fun _ => rfl
  rw [hstep, hgen]
  have htag : algKotlinTag "GameOfLifeStepKt" "stepGeneration" "(Ljava/util/Set;)Ljava/util/Set;" =
      stepGenerationTag := rfl
  have hl : isAlgKotlinLiftedClass "GameOfLifeStepKt" = true := rfl
  have htags : Jvm.parseMethodParamTags "(Ljava/util/Set;)Ljava/util/Set;" = ['L'] := rfl
  have hv : "(Ljava/util/Set;)Ljava/util/Set;".endsWith ")V" = false := by decide +kernel
  have hrun' : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf GameOfLifeStepKt_stepGeneration_prog
      { pc := 0, stack := [],
        locals := (algKotlinParamSlots 0 ['L'] ((Jvm.JvmVal.heapRef cur :: stk).take 1).reverse).foldl
            (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0),
        jvmHeap := jh, heap := hp } = some (res, endSt) := hrun
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, hl, htag, htags, hr, ite_true, Option.map_some,
    List.length_cons, List.length_nil, Nat.zero_add, hrun', algKotlinAfterCall, hv, Bool.false_eq_true, ite_false]
  have hlt : ¬ stk.length + 1 < 1 := by omega
  simp only [hlt, ↓reduceIte, List.drop_succ_cons, List.drop_zero]

theorem mkHooks_eq (rp : String → Option (List JvmInstr)) (d sf : Nat) :
    ∃ ip, mkAlgKotlinHooks rp d sf = algKotlinHooksWith ip := by
  cases d <;> exact ⟨_, rfl⟩

theorem ofNat_succ_sub_one (c : Nat) : UInt32.ofNat (c + 1) - 1 = UInt32.ofNat c := by
  rw [← ofNat_succ]; simp

theorem slt0_ofNat_succ {c : Nat} (hc : c + 1 < 2 ^ 31) : (0#32).slt (UInt32.ofNat (c + 1)).toBitVec = true := by
  simp only [BitVec.slt, BitVec.toInt_zero]
  rw [Jvm.u32_toInt_eq_toNat (by rw [ofNat_toNat_of_lt (by omega)]; omega), ofNat_toNat_of_lt (by omega)]
  exact decide_eq_true (by omega)

section StepGenerations

variable {rp : String → Option (List JvmInstr)} {d sf : Nat} {hp : AlgHeap}

local notation "HM" => mkAlgKotlinHooks rp (d + 1) sf
local notation "Q" => GameOfLifeStepKt_stepGenerations_prog

/-- Locals at the loop head of `stepGenerations` (pc 3). -/
def glocs (base : Nat → JvmVal) (cur : Nat) (c : Nat) : Nat → JvmVal :=
  Jvm.setLocal (Jvm.setLocal base 0 (.heapRef cur)) 1 (.i32 (UInt32.ofNat c))

theorem gens_loop (hr : rp stepGenerationTag = some GameOfLifeStepKt_stepGeneration_prog) :
    ∀ (c : Nat) (base : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (cur ca : Nat) (ccls cec : String)
      (curL : List (Int32 × Int32)), c < 2 ^ 31 →
      IsColl jh cur ccls ca cec curL → (ccls = "java/util/Set" ∨ ccls = "java/util/LinkedHashSet") → curL.Nodup →
      (∀ j < c, 9 * (stepGenerationsLoop j curL).length < 2 ^ 32 ∧
        2000 * ((stepGenerationsLoop j curL).length + 1) ≤ sf) →
      ∃ L jh' res rcls ra rec, Reaches HM Q ⟨3, [], glocs base cur c, jh, hp⟩ ⟨19, [.heapRef res], L, jh', hp⟩
          (c * 14 + 4) ∧
        Frame jh jh' ∧ IsColl jh' res rcls ra rec (stepGenerationsLoop c curL) := by
  intro c
  induction c with
  | zero =>
    intro base jh cur ca ccls cec curL _ hc _ _ _
    refine ⟨glocs base cur 0, jh, cur, ccls, ca, cec, ?_, frame_refl jh, hc⟩
    gs
    refine reaches_ifgt_fall rfl (by decide) ?_
    gs
    gsg
    exact reaches_refl
  | succ c ih =>
    intro base jh cur ca ccls cec curL hc31 hc hcls hnd hb
    obtain ⟨ip, hip⟩ := mkHooks_eq rp d sf
    have h0 := hb 0 (by omega)
    obtain ⟨r, ra, endSt, hrun, hcr, hfr, hhp⟩ := stepGeneration_run (ip := ip) (fun _ => .i32 0) sf (hp := hp)
      hc hcls hnd h0.1 h0.2
    rw [← hip] at hrun
    let jh1 := endSt.jvmHeap
    have hcall := step_call_gen (d := d) (pc := 8) (stk := []) (locs := glocs base cur (c + 1)) hr hrun
    rw [hhp] at hcall
    obtain ⟨L, jh', res, rcls, ra', rec, hR, hf', hc'⟩ := ih
      (Jvm.setLocal (Jvm.setLocal (glocs base cur (c + 1)) 2 (.heapRef r)) 3 (.i32 (UInt32.ofNat c)))
      jh1 r ra "java/util/LinkedHashSet" "java/lang/Object" (stepGenerationModel curL) (by omega) hcr (.inr rfl)
      (stepGenerationModel_nodup curL) (fun j hj => hb (j + 1) (by omega))
    refine ⟨L, jh', res, rcls, ra', rec, ?_, frame_trans hfr hf', hc'⟩
    rw [show (c + 1) * 14 + 4 = (c * 14 + 4) + 14 by omega]
    gs
    refine reaches_ifgt_jump rfl (slt0_ofNat_succ hc31) ?_
    gs
    gsh hcall
    gs; gs; gs; gs
    rw [ofNat_succ_sub_one]
    gs; gs; gs; gs; gs
    gsg
    refine reaches_congr_locs ?_ hR
    funext i
    simp only [glocs, Jvm.setLocal]
    by_cases h1 : i = 1
    · simp [h1]
    · by_cases h0 : i = 0
      · simp [h0]
      · simp [h0, h1]

end StepGenerations

theorem int32_toUInt32_eq_ofNat {step : Int32} (hpos : 0 < step.toInt) :
    step.toUInt32 = UInt32.ofNat step.toInt.toNat := by
  apply UInt32.toNat.inj
  have hti : step.toInt = step.toUInt32.toBitVec.toInt := rfl
  have hlt : step.toUInt32.toNat < 2 ^ 32 := UInt32.toNat_lt _
  have hnn : step.toUInt32.toNat < 2 ^ 31 := by
    rw [BitVec.toInt_eq_toNat_cond] at hti
    split at hti
    · rename_i h; simp only [UInt32.toNat_toBitVec] at h; omega
    · rename_i h; simp only [UInt32.toNat_toBitVec] at h hti; omega
  rw [hti, Jvm.u32_toInt_eq_toNat hnn, Int.toNat_natCast, ofNat_toNat_of_lt hlt]

end GolStep

open GolStep

/--
`stepGeneration(aliveCells)` (JVM equivalence): for an input `Set<IntOffset>` (a modeled `java/util/Set` or
`LinkedHashSet` iterating the distinct cells `alive`), the bytecode returns a fresh `LinkedHashSet` iterating exactly
`stepGenerationModel alive`, in order, leaving every pre-existing heap object unchanged. `9 * alive.length < 2 ^ 32`
keeps the candidate set's 32-bit iterator index in range (a real JVM collection holds fewer than `2 ^ 31` elements).
-/
theorem stepGeneration_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (alive : List (Int32 × Int32)) (hnd : alive.Nodup) (h9 : 9 * alive.length < 2 ^ 32)
    (hf : 2000 * (alive.length + 1) ≤ fuel) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (s sa : Nat)
    (scls sec : String) (hs : IsColl jh s scls sa sec alive)
    (hscls : scls = "java/util/Set" ∨ scls = "java/util/LinkedHashSet") :
    ∃ r ra endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel GameOfLifeStepKt_stepGeneration_prog
          (Jvm.initJvmState [(0, .heapRef s)] (.i32 0) hp jh) = some (.heapRef r, endSt) ∧
      IsColl endSt.jvmHeap r "java/util/LinkedHashSet" ra "java/lang/Object" (stepGenerationModel alive) ∧
      Frame jh endSt.jvmHeap ∧ endSt.heap = hp := by
  obtain ⟨ip, hip⟩ := mkHooks_eq resolveProg d subFuel
  rw [hip]
  exact stepGeneration_run (fun _ => .i32 0) fuel hs hscls hnd h9 hf

/--
`stepGenerations(aliveCells, step)` (JVM equivalence): the bytecode returns a set iterating exactly
`stepGenerationsModel alive step`, leaving every pre-existing heap object unchanged. For `step <= 0` it returns the
input set itself; otherwise it calls the lifted `stepGeneration` program (through `resolveProg`) `step` times. The
domain: `alive` is the distinct cells of the input `Set<IntOffset>`, and every generation the loop feeds to
`stepGeneration` has at most `P` cells with `9 * P < 2 ^ 32`, each call running within `subFuel` steps.
-/
theorem stepGenerations_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : resolveProg stepGenerationTag = some GameOfLifeStepKt_stepGeneration_prog) (d subFuel fuel : Nat)
    (alive : List (Int32 × Int32)) (step : Int32) (hnd : alive.Nodup) (P : Nat)
    (hP : ∀ j < step.toInt.toNat, (stepGenerationsLoop j alive).length ≤ P) (h9 : 9 * P < 2 ^ 32)
    (hsf : 2000 * (P + 1) ≤ subFuel) (hf : 14 * step.toInt.toNat + 8 ≤ fuel)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (s sa : Nat) (scls sec : String) (hs : IsColl jh s scls sa sec alive)
    (hscls : scls = "java/util/Set" ∨ scls = "java/util/LinkedHashSet") :
    ∃ r rcls ra rec endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg (d + 1) subFuel) fuel GameOfLifeStepKt_stepGenerations_prog
          (Jvm.initJvmState [(0, .heapRef s), (1, .i32 step.toUInt32)] (.i32 0) hp jh) = some (.heapRef r, endSt) ∧
      IsColl endSt.jvmHeap r rcls ra rec (stepGenerationsModel alive step) ∧
      Frame jh endSt.jvmHeap ∧ endSt.heap = hp := by
  by_cases hpos : step.toInt ≤ 0
  · have hm : stepGenerationsModel alive step = alive := by simp [stepGenerationsModel, hpos]
    rw [hm]
    have hslt : (0#32).slt step.toUInt32.toBitVec = false := by
      have hti : step.toInt = step.toUInt32.toBitVec.toInt := rfl
      simp only [BitVec.slt, BitVec.toInt_zero]
      exact decide_eq_false (by omega)
    have hR : Reaches (mkAlgKotlinHooks resolveProg (d + 1) subFuel) GameOfLifeStepKt_stepGenerations_prog
        (Jvm.initJvmState [(0, .heapRef s), (1, .i32 step.toUInt32)] (.i32 0) hp jh)
        ⟨19, [.heapRef s], Jvm.setLocal (Jvm.setLocal (fun _ => .i32 0) 0 (.heapRef s)) 1 (.i32 step.toUInt32),
          jh, hp⟩ 7 := by
      gs; gs; gs; gs
      refine reaches_ifgt_fall rfl hslt ?_
      gs
      gsg
      exact reaches_refl
    exact ⟨s, scls, sa, sec, _, run_of_reaches_ret hR rfl rfl (by omega), hs, frame_refl jh, rfl⟩
  · have hpos' : 0 < step.toInt := by omega
    have hm : stepGenerationsModel alive step = stepGenerationsLoop step.toInt.toNat alive := by
      simp [stepGenerationsModel, hpos]
    rw [hm]
    have hc31 : step.toInt.toNat < 2 ^ 31 := by
      have := Int32.toInt_lt step
      omega
    obtain ⟨L, jh', res, rcls, ra, rec, hR, hf', hc'⟩ := gens_loop (d := d) (sf := subFuel) (hp := hp) hr
      step.toInt.toNat (fun _ => .i32 0) jh s sa scls sec alive hc31 hs hscls hnd
      (fun j hj => ⟨by have := hP j hj; omega, by have := hP j hj; omega⟩)
    have hR0 : Reaches (mkAlgKotlinHooks resolveProg (d + 1) subFuel) GameOfLifeStepKt_stepGenerations_prog
        (Jvm.initJvmState [(0, .heapRef s), (1, .i32 step.toUInt32)] (.i32 0) hp jh)
        ⟨19, [.heapRef res], L, jh', hp⟩ (step.toInt.toNat * 14 + 4 + 3) := by
      gs; gs; gs
      rw [int32_toUInt32_eq_ofNat hpos']
      exact hR
    exact ⟨res, rcls, ra, rec, _, run_of_reaches_ret hR0 rfl rfl (by omega), hc', hf', rfl⟩

end Algorithm.KotlinJvmVerification
