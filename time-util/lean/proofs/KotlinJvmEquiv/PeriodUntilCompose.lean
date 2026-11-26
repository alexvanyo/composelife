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

import proofs.KotlinJvmEquiv.PeriodUntil

namespace TimeUtil.KotlinJvmVerification

open TimeUtil.JvmVerification
open TimeUtil.KotlinJvmBytecode
open TimeUtil.Model

/-! # `@Composable` `periodUntil` / `progressivePeriodUntil`: initial composition

On the first composition (an empty slot table: no groups, no open group frame), each of the four composables

* reads the clock exactly once and computes its initial value with the (separately verified) helper
  `periodUntilWithUnit` / `periodUntilWithProgressiveUnits`,
* remembers that value, allocates the `produceState` producer closure capturing its arguments, and
* returns the produced state's initial value, i.e. the helper's model value for that clock reading,

for every trace flag and every `$changed` bit pattern (the `$changed` bits only decide whether the clock or unit
list is also recorded with `changedInstance`, which does not affect the result). The producer coroutine that later
updates the state is a separate class and is not modeled.

The proofs step the lifted bytecode with the `time_step_blk` block stepper and dedicated step lemmas for each
Compose runtime operation on the slot-table model (`startMovableGroup`, `rememberedValue`, `updateRememberedValue`,
`changedInstance`, `produceState`, `State.getValue`, `endMovableGroup`). The trace prologue/epilogue and the
`$changed`-bit segments are stated generically with the composer state in closed form, so no proof case-splits on
the symbolic trace flag or `$changed` bits.
-/

section ComposerSteps

theorem iface_composer_eq (hooks : Jvm.JvmHooks TimeExt TimeHeap) (st : JvmState) (m desc : String) :
    Jvm.stepInvokeInterfaceGeneric hooks st "androidx/compose/runtime/Composer" m desc =
      hooks.stepInvokeInterface st "androidx/compose/runtime/Composer" m desc := by
  unfold Jvm.stepInvokeInterfaceGeneric
  split <;> first | rfl | (exfalso; simp_all)

theorem iface_state_eq (hooks : Jvm.JvmHooks TimeExt TimeHeap) (st : JvmState) (m desc : String) :
    Jvm.stepInvokeInterfaceGeneric hooks st "androidx/compose/runtime/State" m desc =
      hooks.stepInvokeInterface st "androidx/compose/runtime/State" m desc := by
  unfold Jvm.stepInvokeInterfaceGeneric
  split <;> first | rfl | (exfalso; simp_all)

theorem stepComposer_getValue (st : JvmState) (desc : String) :
    stepComposerInterface st "getValue" desc = .inr none := by
  unfold stepComposerInterface
  split <;> first | rfl | (exfalso; simp_all)

variable {resolveProg : String → Option (List JvmInstr)} {d subFuel f pc pc0 : Nat}
  {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt}
  {ins tr : Bool} {cells : List (Nat × JvmVal)} {nid : Nat} {cl : Array (String × List JvmVal)} {r : Nat}
  {now : Nat → Int64} {ut : Int64 → Int64 → Model.DateTimeUnit → String → Int64}
  {utm : Int64 → Int64 → Model.TimeBasedUnit → Int64} {gs : List (Compose.GroupEntry JvmVal)}
  {gst : List Compose.ActiveGroupFrame}

/-! #### Compose runtime operations on the slot-table model -/

theorem runFast_startMovableGroup_fresh {dk : JvmVal} {key : UInt32} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "startMovableGroup" "(ILjava/lang/Object;)V" :: rest)
        ⟨pc0, dk :: .i32 key :: .ext .composer :: stk, locs, jh,
          ⟨⟨ins, [], [], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh,
          ⟨⟨ins, [⟨key.toInt32, []⟩], [⟨key.toInt32, ([] : List JvmVal).length, none⟩], cells, nid, tr⟩,
            cl, r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokeinterface_step
  rfl

theorem runFast_rememberedValue {K : Int32} {sl : List JvmVal} {li : Option Nat} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "rememberedValue" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext .composer :: stk, locs, jh,
          ⟨⟨ins, [⟨K, sl⟩], [⟨K, sl.length, li⟩], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext .composerEmpty :: stk, locs, jh,
          ⟨⟨ins, [⟨K, sl⟩], [⟨K, sl.length + 1, some sl.length⟩], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokeinterface_step
  rw [iface_composer_eq]
  dsimp only [mkTimeHooks]
  simp only [stepComposerInterface]
  have h : Compose.readRememberSlot
      (⟨ins, [⟨K, sl⟩], [⟨K, sl.length, li⟩], cells, nid, tr⟩ : Compose.ComposerModel JvmVal) =
      (none, ⟨ins, [⟨K, sl⟩], [⟨K, sl.length + 1, some sl.length⟩], cells, nid, tr⟩) := by
    simp [Compose.readRememberSlot, Compose.findGroup?]
  rw [h]
  rfl

theorem runFast_updateRememberedValue {K : Int32} {sl : List JvmVal} {v : JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "updateRememberedValue" "(Ljava/lang/Object;)V" ::
          rest)
        ⟨pc0, v :: .ext .composer :: stk, locs, jh,
          ⟨⟨ins, [⟨K, sl⟩], [⟨K, sl.length + 1, some sl.length⟩], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh,
          ⟨⟨ins, [⟨K, sl ++ [v]⟩], [⟨K, (sl ++ [v]).length, none⟩], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokeinterface_step
  rw [iface_composer_eq]
  dsimp only [mkTimeHooks]
  simp only [stepComposerInterface]
  have h : Compose.writeRememberSlot
      (⟨ins, [⟨K, sl⟩], [⟨K, sl.length + 1, some sl.length⟩], cells, nid, tr⟩ : Compose.ComposerModel JvmVal) v =
      ⟨ins, [⟨K, sl ++ [v]⟩], [⟨K, (sl ++ [v]).length, none⟩], cells, nid, tr⟩ := by
    simp [Compose.writeRememberSlot, Compose.findGroup?, Compose.updateGroup]
  rw [h]

theorem runFast_changedInstance {K : Int32} {sl : List JvmVal} {li : Option Nat} {v : JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "changedInstance" "(Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, v :: .ext .composer :: stk, locs, jh,
          ⟨⟨ins, [⟨K, sl⟩], [⟨K, sl.length, li⟩], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 1 :: stk, locs, jh,
          ⟨⟨ins, [⟨K, sl ++ [v]⟩], [⟨K, (sl ++ [v]).length, li⟩], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokeinterface_step
  rw [iface_composer_eq]
  dsimp only [mkTimeHooks]
  simp only [stepComposerInterface]
  have h : Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqTimeExt)
      (⟨ins, [⟨K, sl⟩], [⟨K, sl.length, li⟩], cells, nid, tr⟩ : Compose.ComposerModel JvmVal) v =
      (true, ⟨ins, [⟨K, sl ++ [v]⟩], [⟨K, (sl ++ [v]).length, li⟩], cells, nid, tr⟩) := by
    simp [Compose.checkChangedSlot, Compose.findGroup?, Compose.updateGroup]
  rw [h]
  rfl

theorem runFast_clockNow {C : Compose.ComposerModel JvmVal} {cid : Nat} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "kotlin/time/Clock" "now" "()Lkotlin/time/Instant;" :: rest)
        ⟨pc0, .ext (.clock cid) :: stk, locs, jh, ⟨C, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.instant (now r)) :: stk, locs, jh, ⟨C, cl, r + 1, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokeinterface_step
  rfl

theorem runFast_produceState {ch prod init : JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/SnapshotStateKt" "produceState"
          "(Ljava/lang/Object;Lkotlin/jvm/functions/Function2;Landroidx/compose/runtime/Composer;I)Landroidx/compose/runtime/State;" ::
          rest)
        ⟨pc0, ch :: .ext .composer :: prod :: init :: stk, locs, jh,
          ⟨⟨ins, gs, gst, cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.stateRef nid) :: stk, locs, jh,
          ⟨⟨ins, gs, gst, (nid, init) :: cells, nid + 1, tr⟩, cl, r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokestatic_step
  rfl

theorem runFast_stateGetValue {sid nid' : Nat} {v : JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/State" "getValue" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.stateRef sid) :: stk, locs, jh,
          ⟨⟨ins, gs, gst, (sid, v) :: cells, nid', tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, ⟨⟨ins, gs, gst, (sid, v) :: cells, nid', tr⟩, cl, r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokeinterface_step
  rw [iface_state_eq]
  dsimp only [mkTimeHooks]
  rw [stepComposer_getValue]
  have h : Compose.readState (⟨ins, gs, gst, (sid, v) :: cells, nid', tr⟩ : Compose.ComposerModel JvmVal) sid =
      some v := by
    simp [Compose.readState]
  simp only [h]

theorem runFast_endMovableGroup {fr : Compose.ActiveGroupFrame} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "endMovableGroup" "()V" :: rest)
        ⟨pc0, .ext .composer :: stk, locs, jh,
          ⟨⟨ins, gs, fr :: gst, cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, ⟨⟨ins, gs, gst, cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokeinterface_step
  rfl

/-! #### Simple instruction steps with explicit results -/

theorem runFast_load {n : Nat} {v : JvmVal} {hp : TimeHeap} (instr : JvmInstr)
    (hi : instr = .iload n ∨ instr = .aload n) (hv : locs n = v) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (instr :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  rcases hi with rfl | rfl <;>
  · apply Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) _ rfl
    rw [← hv]
    rfl

theorem runFast_iconst {c : UInt32} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.iconst c :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) rfl rfl

theorem runFast_iand {a b : UInt32} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.iand :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (a &&& b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) rfl rfl

theorem runFast_ixor {a b : UInt32} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ixor :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (a ^^^ b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) rfl rfl

theorem runFast_goto' {t : Nat} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.goto t :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog t (prog.drop t) ⟨t, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
  rfl

theorem runFast_if_icmple' {t : Nat} {a b : UInt32} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.if_icmple t :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      if a.toBitVec.sle b.toBitVec then
        Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog t (prog.drop t) ⟨t, stk, locs, jh, hp⟩
      else Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmple]

theorem runFast_if_icmpne' {t : Nat} {a b : UInt32} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.if_icmpne t :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      if !(a == b) then
        Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog t (prog.drop t) ⟨t, stk, locs, jh, hp⟩
      else Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpne]

theorem runFast_ifne_one {t : Nat} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifne t :: rest)
        ⟨pc0, .i32 1 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog t (prog.drop t) ⟨t, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifne]
  rfl

theorem runFast_ifne_nz {t : Nat} {v : UInt32} {hp : TimeHeap} (hnz : (v == 0) = false) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifne t :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog t (prog.drop t) ⟨t, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifne, hnz]
  rfl

theorem runFast_isTrace {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if hp.composer.traceEnabled then 1 else 0) :: stk, locs, jh, hp⟩ := by
  apply Jvm.runJvmResFast_invokestatic_step
  rfl

theorem runFast_ifeq_lit {t : Nat} {c : UInt32} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifeq t :: rest)
        ⟨pc0, .i32 c :: stk, locs, jh, hp⟩ =
      if c == 0 then
        Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog t (prog.drop t) ⟨t, stk, locs, jh, hp⟩
      else Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]

theorem runFast_traceEventStart {a b c e : JvmVal} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "traceEventStart" "(IIILjava/lang/String;)V" :: rest)
        ⟨pc0, a :: b :: c :: e :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  apply Jvm.runJvmResFast_invokestatic_step
  rfl

theorem runFast_traceEventEnd {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "traceEventEnd" "()V" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  apply Jvm.runJvmResFast_invokestatic_step
  rfl

theorem runFast_markerEnd {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformationMarkerEnd"
          "(Landroidx/compose/runtime/Composer;)V" :: rest)
        ⟨pc0, .ext .composer :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  apply Jvm.runJvmResFast_invokestatic_step
  rfl

theorem runFast_areturn' {v : JvmVal} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.areturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .areturn rest _ rfl (by simp)]
  cases d <;> rfl

/-! #### Trace prologue/epilogue and `$changed`-bit segments -/

/-- Whether the `$changed` bits leave the parameter's stability uncertain, so the composable calls
`changedInstance` on it (the `$changed & m1 ^ x1 > c1` test). -/
def changedSlotChecked (changed m1 x1 c1 : UInt32) : Bool :=
  !(((changed &&& m1) ^^^ x1).toBitVec.sle c1.toBitVec)

/-- The value the `$changed`-bit segment pushes on the first composition (where `changedInstance` is true). -/
def changedBit (changed m1 x1 c1 m2 c2 : UInt32) : UInt32 :=
  if changedSlotChecked changed m1 x1 c1 then 1 else if (changed &&& m2) == c2 then 1 else 0

/-- The remember slots after the `$changed`-bit segment. -/
def slotsAfterChanged (changed m1 x1 c1 : UInt32) (sl : List JvmVal) (v : JvmVal) : List JvmVal :=
  if changedSlotChecked changed m1 x1 c1 then sl ++ [v] else sl

theorem runFast_traceStart {F t n : Nat} {K X : UInt32} {s : String}
    (ht : t = pc + 7) (hrest : prog.drop t = rest) (hF : F = f + 7) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) F prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z" :: .ifeq t ::
          .iconst K :: .iload n :: .iconst X :: .ldcStr s ::
          .invokestatic "androidx/compose/runtime/ComposerKt" "traceEventStart" "(IIILjava/lang/String;)V" :: rest)
        ⟨pc0, stk, locs, jh, ⟨⟨ins, gs, gst, cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel)
        ((if tr then 0 else 5) + f) prog t (prog.drop t)
        ⟨t, stk, locs, jh, ⟨⟨ins, gs, gst, cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ := by
  subst hF
  rw [runFast_isTrace, runFast_ifeq_lit]
  cases tr
  · simp only [Bool.false_eq_true, ↓reduceIte, Jvm.ui32_beq_0_0]
    rw [Nat.add_comm 5 f]
  · simp only [↓reduceIte, Jvm.ui32_beq_1_0, Bool.false_eq_true]
    rw [runFast_iconst, runFast_load _ (Or.inl rfl) rfl, runFast_iconst,
      Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) rfl rfl, runFast_traceEventStart, Nat.zero_add]
    subst ht
    rw [hrest]

theorem runFast_traceEnd {F t c ret : Nat} {v : JvmVal} {hp : TimeHeap} {rest' : List JvmInstr}
    (ht : t = pc + 3)
    (hrest : prog.drop t = .aload c ::
      .invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformationMarkerEnd"
        "(Landroidx/compose/runtime/Composer;)V" :: .aload ret :: .areturn :: rest')
    (hc : locs c = .ext .composer) (hv : locs ret = v) (hF : F = f + 7) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) F prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z" :: .ifeq t ::
          .invokestatic "androidx/compose/runtime/ComposerKt" "traceEventEnd" "()V" :: .aload c ::
          .invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformationMarkerEnd"
            "(Landroidx/compose/runtime/Composer;)V" :: .aload ret :: .areturn :: rest')
        ⟨pc0, stk, locs, jh, hp⟩ =
      some (v, ⟨t + 3, v :: stk, locs, jh, hp⟩) := by
  subst ht hF
  rw [runFast_isTrace, runFast_ifeq_lit]
  cases htr : hp.composer.traceEnabled
  · simp only [Bool.false_eq_true, ↓reduceIte, Jvm.ui32_beq_0_0]
    rw [hrest, runFast_load _ (Or.inr rfl) hc, runFast_markerEnd, runFast_load _ (Or.inr rfl) hv,
      runFast_areturn']
  · simp only [↓reduceIte, Jvm.ui32_beq_1_0, Bool.false_eq_true]
    rw [runFast_traceEventEnd, runFast_load _ (Or.inr rfl) hc, runFast_markerEnd,
      runFast_load _ (Or.inr rfl) hv, runFast_areturn']

theorem runFast_changedSeg {F q p0 n c a : Nat} {changed m1 x1 c1 m2 c2 : UInt32} {va : JvmVal}
    {K : Int32} {sl : List JvmVal} {li : Option Nat}
    (hn : locs n = .i32 changed) (hc : locs c = .ext .composer) (ha : locs a = va)
    (hd1 : prog.drop (q + 5) = .iload n :: .iconst m2 :: .iand :: .iconst c2 :: .if_icmpne (q + 12) ::
      .iconst 1 :: .goto (q + 13) :: .iconst 0 :: rest)
    (hd2 : prog.drop (q + 10) = .iconst 1 :: .goto (q + 13) :: .iconst 0 :: rest)
    (hd3 : prog.drop (q + 12) = .iconst 0 :: rest)
    (hd4 : prog.drop (q + 13) = rest) (hF : F = f + 8) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) F prog q
        (.if_icmple (q + 5) :: .aload c :: .aload a ::
          .invokeinterface "androidx/compose/runtime/Composer" "changedInstance" "(Ljava/lang/Object;)Z" ::
          .ifne (q + 10) :: .iload n :: .iconst m2 :: .iand :: .iconst c2 :: .if_icmpne (q + 12) ::
          .iconst 1 :: .goto (q + 13) :: .iconst 0 :: rest)
        ⟨p0, .i32 c1 :: .i32 ((changed &&& m1) ^^^ x1) :: stk, locs, jh,
          ⟨⟨ins, [⟨K, sl⟩], [⟨K, sl.length, li⟩], cells, nid, tr⟩, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel)
        ((if !changedSlotChecked changed m1 x1 c1 && (changed &&& m2) == c2 then 0 else 1) + f) prog (q + 13)
        rest
        ⟨q + 13, .i32 (changedBit changed m1 x1 c1 m2 c2) :: stk, locs, jh,
          ⟨⟨ins, [⟨K, slotsAfterChanged changed m1 x1 c1 sl va⟩],
            [⟨K, (slotsAfterChanged changed m1 x1 c1 sl va).length, li⟩], cells, nid, tr⟩,
            cl, r, now, ut, utm⟩⟩ := by
  subst hF
  rw [runFast_if_icmple']
  cases hA : changedSlotChecked changed m1 x1 c1
  · have hle : ((changed &&& m1) ^^^ x1).toBitVec.sle c1.toBitVec = true := by
      simpa [changedSlotChecked] using hA
    simp only [hle, ↓reduceIte]
    rw [hd1, runFast_load _ (Or.inl rfl) hn, runFast_iconst, runFast_iand, runFast_iconst,
      runFast_if_icmpne']
    cases hB : (changed &&& m2) == c2
    · simp only [Bool.not_false, ↓reduceIte]
      rw [hd3, runFast_iconst]
      simp only [changedBit, slotsAfterChanged, hA, hB, Bool.false_eq_true, ↓reduceIte, Bool.and_false]
      rw [Nat.add_comm 1 f]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [runFast_iconst, runFast_goto', hd4]
      simp only [changedBit, slotsAfterChanged, hA, hB, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.and_self, Nat.zero_add]
  · have hle : ((changed &&& m1) ^^^ x1).toBitVec.sle c1.toBitVec = false := by
      simpa [changedSlotChecked] using hA
    simp only [hle, Bool.false_eq_true, ↓reduceIte]
    rw [runFast_load _ (Or.inr rfl) hc, runFast_load _ (Or.inr rfl) ha, runFast_changedInstance, runFast_ifne_one,
      hd2, runFast_iconst, runFast_goto', hd4]
    simp only [changedBit, slotsAfterChanged, hA, ↓reduceIte, Bool.not_true, Bool.false_and,
      Bool.false_eq_true]
    rw [Nat.add_comm 1 f]

theorem runFast_initClosure_periodUntil {cont clockV tzV thisV unitV : JvmVal} {a1 a2 : String}
    {C : Compose.ComposerModel JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/timeutil/PeriodUntilKt$periodUntil$2$1" "<init>"
          "(Lkotlinx/datetime/DateTimeUnit;Lkotlin/time/Instant;Lkotlinx/datetime/TimeZone;Lkotlin/time/Clock;Lkotlin/coroutines/Continuation;)V" ::
          rest)
        ⟨pc0, cont :: clockV :: tzV :: thisV :: unitV :: .allocRef a1 :: .allocRef a2 :: stk, locs, jh,
          ⟨C, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cl.size) :: stk, locs, jh,
          ⟨C, cl.push ("PeriodUntilKt$periodUntil$2$1", [unitV, thisV, tzV, clockV]), r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokespecial_step
  rfl

theorem runFast_initClosure_periodUntil_1 {cont clockV unitV thisV : JvmVal} {a1 a2 : String}
    {C : Compose.ComposerModel JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/timeutil/PeriodUntilKt$periodUntil$4$1" "<init>"
          "(Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;Lkotlin/time/Clock;Lkotlin/coroutines/Continuation;)V" ::
          rest)
        ⟨pc0, cont :: clockV :: unitV :: thisV :: .allocRef a1 :: .allocRef a2 :: stk, locs, jh,
          ⟨C, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cl.size) :: stk, locs, jh,
          ⟨C, cl.push ("PeriodUntilKt$periodUntil$4$1", [thisV, unitV, clockV]), r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokespecial_step
  rfl

theorem runFast_initClosure_progressivePeriodUntil {cont tzV thisV clockV listV : JvmVal} {a1 a2 : String}
    {C : Compose.ComposerModel JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/timeutil/PeriodUntilKt$progressivePeriodUntil$2$1" "<init>"
          "(Ljava/util/List;Lkotlin/time/Clock;Lkotlin/time/Instant;Lkotlinx/datetime/TimeZone;Lkotlin/coroutines/Continuation;)V" ::
          rest)
        ⟨pc0, cont :: tzV :: thisV :: clockV :: listV :: .allocRef a1 :: .allocRef a2 :: stk, locs, jh,
          ⟨C, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cl.size) :: stk, locs, jh,
          ⟨C, cl.push ("PeriodUntilKt$progressivePeriodUntil$2$1", [listV, clockV, thisV, tzV]),
            r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokespecial_step
  rfl

theorem runFast_initClosure_progressivePeriodUntil_1 {cont thisV clockV listV : JvmVal} {a1 a2 : String}
    {C : Compose.ComposerModel JvmVal} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/timeutil/PeriodUntilKt$progressivePeriodUntil$4$1" "<init>"
          "(Ljava/util/List;Lkotlin/time/Clock;Lkotlin/time/Instant;Lkotlin/coroutines/Continuation;)V" ::
          rest)
        ⟨pc0, cont :: thisV :: clockV :: listV :: .allocRef a1 :: .allocRef a2 :: stk, locs, jh,
          ⟨C, cl, r, now, ut, utm⟩⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cl.size) :: stk, locs, jh,
          ⟨C, cl.push ("PeriodUntilKt$progressivePeriodUntil$4$1", [listV, clockV, thisV]), r, now, ut, utm⟩⟩ := by
  apply Jvm.runJvmResFast_invokespecial_step
  rfl

end ComposerSteps



/-! ### Calls to the progressive helpers from a composable -/

theorem lookup_periodUntilWithProgressiveUnits :
    timeProgLookup
      "PeriodUntilKt.periodUntilWithProgressiveUnits:(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;Lkotlinx/datetime/TimeZone;)Lkotlin/Pair;" =
      some PeriodUntilKt_periodUntilWithProgressiveUnits_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem lookup_periodUntilWithProgressiveUnits_1 :
    timeProgLookup
      "PeriodUntilKt.periodUntilWithProgressiveUnits:(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;)Lkotlin/Pair;" =
      some PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

set_option maxRecDepth 4096 in
theorem tags_periodUntilWithProgressiveUnits :
    Jvm.parseMethodParamTags
      "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;Lkotlinx/datetime/TimeZone;)Lkotlin/Pair;" =
      ['L', 'L', 'L', 'L'] := by decide

set_option maxRecDepth 4096 in
theorem tags_periodUntilWithProgressiveUnits_1 :
    Jvm.parseMethodParamTags "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;)Lkotlin/Pair;" =
      ['L', 'L', 'L'] := by decide

/-- Calling `periodUntilWithProgressiveUnits` (with a time zone) from a composable: the call returns the model's
pair; the JVM heap afterwards (holding the helper's temporary lists) keeps clean statics. -/
theorem runFast_call_periodUntilWithProgressiveUnits {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg) {d1 subFuel : Nat} (hd1 : 3 ≤ d1) (hsf : 50 ≤ subFuel)
    {start other : Int64} {units : List DateTimeUnit} {tz : String}
    (hneUnits : units ≠ []) (hlen31 : units.length < 2 ^ 31) (hfuel : 70 * units.length + 70 ≤ subFuel)
    {hp : TimeHeap}
    (hNotMin : ∀ u ∈ units, periodNoAbsMin (periodUntilWithUnitModel (hp.untilTz start other u tz) u) u)
    {listAddr arrAddr : Nat} {jh : Jvm.JvmHeap TimeExt} (hc : HasTimeStaticsClean jh)
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray)) :
    ∃ resPair jh',
      periodUntilWithProgressiveUnitsModel
          (units.map fun u => (u, periodUntilWithUnitModel (hp.untilTz start other u tz) u)) = some resPair ∧
      HasTimeStaticsClean jh' ∧
      ∀ (f pc pc0 : Nat) (prog rest : List JvmInstr) (stk : List JvmVal) (locs : Nat → JvmVal),
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
            (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithProgressiveUnits"
              "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;Lkotlinx/datetime/TimeZone;)Lkotlin/Pair;" ::
              rest)
            ⟨pc0, .ext (.timeZone tz) :: .heapRef listAddr :: .ext (.instant other) :: .ext (.instant start) :: stk,
              locs, jh, hp⟩ =
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
            ⟨pc + 1, .pair (.ext (.timeUnit resPair.1)) (.ext (.period resPair.2)) :: stk, locs, jh', hp⟩ := by
  obtain ⟨resPair, endSt, hmod, hrun, hcEnd, hhp⟩ :=
    periodUntilWithProgressiveUnits_equiv resolveProg hext d1 subFuel subFuel hd1 hsf start other units tz
      hneUnits hlen31 hfuel hp hNotMin listAddr arrAddr jh hc hlist harr
  refine ⟨resPair, endSt.jvmHeap, hmod, hcEnd, ?_⟩
  intro f pc pc0 prog rest stk locs
  have hprog : resolveProg
      "PeriodUntilKt.periodUntilWithProgressiveUnits:(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;Lkotlinx/datetime/TimeZone;)Lkotlin/Pair;" =
      some PeriodUntilKt_periodUntilWithProgressiveUnits_prog := hext _ _ lookup_periodUntilWithProgressiveUnits
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithProgressiveUnits"
        "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;Lkotlinx/datetime/TimeZone;)Lkotlin/Pair;")
      ⟨pc, .ext (.timeZone tz) :: .heapRef listAddr :: .ext (.instant other) :: .ext (.instant start) :: stk,
        locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .pair (.ext (.timeUnit resPair.1)) (.ext (.period resPair.2)) :: stk, locs,
        endSt.jvmHeap, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.timeZone tz) :: .heapRef listAddr :: .ext (.instant other) :: .ext (.instant start) :: stk,
        locs, jh, hp⟩)
      (method := "periodUntilWithProgressiveUnits")
      (desc := "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;Lkotlinx/datetime/TimeZone;)Lkotlin/Pair;")
      (tags := ['L', 'L', 'L', 'L'])
      (args := [.ext (.instant start), .ext (.instant other), .heapRef listAddr, .ext (.timeZone tz)])
      (stkRest := stk) (res := unitPairVal resPair.1 resPair.2) (endSt := endSt)
      tags_periodUntilWithProgressiveUnits rfl rfl hprog hrun
    rw [hs, hhp]
    rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

/-- Calling `periodUntilWithProgressiveUnits` (`TimeBased` units) from a composable. -/
theorem runFast_call_periodUntilWithProgressiveUnits_1 {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg) {d1 subFuel : Nat} (hd1 : 3 ≤ d1) (hsf : 50 ≤ subFuel)
    {start other : Int64} {units : List TimeBasedUnit}
    (hneUnits : units ≠ []) (hlen31 : units.length < 2 ^ 31) (hfuel : 70 * units.length + 70 ≤ subFuel)
    {hp : TimeHeap}
    (hNotMin : ∀ u ∈ units, timePeriodNoAbsMin (periodUntilWithUnitTimeModel (hp.untilTime start other u) u) u)
    {listAddr arrAddr : Nat} {jh : Jvm.JvmHeap TimeExt} (hc : HasTimeStaticsClean jh)
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray)) :
    ∃ resPair jh',
      periodUntilWithProgressiveUnitsTimeModel
          (units.map fun u => (u, periodUntilWithUnitTimeModel (hp.untilTime start other u) u)) = some resPair ∧
      HasTimeStaticsClean jh' ∧
      ∀ (f pc pc0 : Nat) (prog rest : List JvmInstr) (stk : List JvmVal) (locs : Nat → JvmVal),
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
            (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithProgressiveUnits"
              "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;)Lkotlin/Pair;" :: rest)
            ⟨pc0, .heapRef listAddr :: .ext (.instant other) :: .ext (.instant start) :: stk, locs, jh, hp⟩ =
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
            ⟨pc + 1, .pair (.ext (.timeUnit (.timeBased resPair.1))) (.ext (.period resPair.2)) :: stk, locs, jh',
              hp⟩ := by
  obtain ⟨resPair, endSt, hmod, hrun, hcEnd, hhp⟩ :=
    periodUntilWithProgressiveUnits_1_equiv resolveProg hext d1 subFuel subFuel hd1 hsf start other units
      hneUnits hlen31 hfuel hp hNotMin listAddr arrAddr jh hc hlist harr
  refine ⟨resPair, endSt.jvmHeap, hmod, hcEnd, ?_⟩
  intro f pc pc0 prog rest stk locs
  have hprog : resolveProg
      "PeriodUntilKt.periodUntilWithProgressiveUnits:(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;)Lkotlin/Pair;" =
      some PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog := hext _ _ lookup_periodUntilWithProgressiveUnits_1
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithProgressiveUnits"
        "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;)Lkotlin/Pair;")
      ⟨pc, .heapRef listAddr :: .ext (.instant other) :: .ext (.instant start) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .pair (.ext (.timeUnit (.timeBased resPair.1))) (.ext (.period resPair.2)) :: stk, locs,
        endSt.jvmHeap, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .heapRef listAddr :: .ext (.instant other) :: .ext (.instant start) :: stk, locs, jh, hp⟩)
      (method := "periodUntilWithProgressiveUnits")
      (desc := "(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;)Lkotlin/Pair;")
      (tags := ['L', 'L', 'L'])
      (args := [.ext (.instant start), .ext (.instant other), .heapRef listAddr])
      (stkRest := stk) (res := unitTimePairVal resPair.1 resPair.2) (endSt := endSt)
      tags_periodUntilWithProgressiveUnits_1 rfl rfl hprog hrun
    rw [hs, hhp]
    rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

section Tactics

open Lean Elab Tactic Meta

/-- Closes every goal after the main one by `rfl` (default transparency), keeping the main goal first. -/
elab "close_side_rfl" : tactic => do
  let gs ← getGoals
  match gs with
  | [] => return
  | g :: rest =>
    let mut keep : Array MVarId := #[g]
    for s in rest do
      if ← s.isAssigned then continue
      try s.refl catch _ => keep := keep.push s
    setGoals (← keep.toList.filterM fun m => return !(← m.isAssigned))

/-- Runs `tac` on every goal after the main one, keeping the goals it does not close. -/
elab "side_goals " tac:tacticSeq : tactic => do
  let gs ← getGoals
  match gs with
  | [] => return
  | g :: rest =>
    let mut keep : Array MVarId := #[g]
    for s in rest do
      if ← s.isAssigned then continue
      setGoals [s]
      try
        evalTactic tac
        keep := keep ++ (← getGoals).toArray
      catch _ => keep := keep.push s
    setGoals keep.toList

/-- Normalizes the fast-run arguments, rewrites with the given step lemmas, closes their side conditions by `rfl`,
and continues with the block stepper. -/
macro "trw " "[" ts:Lean.Parser.Tactic.rwRule,* "]" : tactic =>
  `(tactic| (time_norm_run_args; rw [$ts,*]; close_side_rfl; time_step_blk))

/-- `time_rfl_step` after normalizing the fast-run arguments. -/
macro "trfl" : tactic => `(tactic| (time_norm_run_args; time_rfl_step))

end Tactics

/-- `Instant.periodUntil(clock, unit, timeZone)` on its first composition returns the period of whole `unit`s from
`this` to one clock reading, remembers it as the produced state's initial value, and allocates the producer. -/
theorem periodUntil_initialComposition_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 50 ≤ subFuel) (hf : 200 ≤ fuel)
    (start : Int64) (clockId : Nat) (u : DateTimeUnit) (tz : String) (changed : UInt32)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
    (hgroups : hp.composer.groups = []) (hstack : hp.composer.groupStack = []) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_periodUntil_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)),
          (2, .ext (.timeUnit u)), (3, .ext (.timeZone tz)), (4, .ext .composer), (5, .i32 changed)] hp jh) =
        some (.ext (.period (periodUntilWithUnitModel
          (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u)), endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.clockReads = hp.clockReads + 1 ∧
      endSt.heap.closures = hp.closures.push ("PeriodUntilKt$periodUntil$2$1",
        [.ext (.timeUnit u), .ext (.instant start), .ext (.timeZone tz), .ext (.clock clockId)]) ∧
      endSt.heap.composer.stateCells = (hp.composer.nextStateId, .ext (.period (periodUntilWithUnitModel
          (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u))) :: hp.composer.stateCells ∧
      endSt.heap.composer.groupStack = [] := by
  obtain ⟨d1, rfl⟩ : ∃ d1, d = d1 + 1 := ⟨d - 1, by omega⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨⟨ins, groups, gstack, cells, nid, trace⟩, closures, reads, now, untilTz, untilTime⟩ := hp
  dsimp only at hgroups hstack ⊢
  subst hgroups hstack
  apply Exists.intro
  refine ⟨Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl ?_, ?_⟩
  simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntil_prog]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  trfl
  trw [runFast_traceStart rfl]
  trfl
  trfl
  trfl
  trw [runFast_startMovableGroup_fresh]
  trfl
  trfl
  trw [runFast_rememberedValue]
  trw [runFast_getstatic_clean (hc _ _) (by rfl)]
  trfl
  trw [runFast_if_acmpne_fallthrough rfl]
  trw [runFast_clockNow]
  trw [runFast_call_periodUntilWithUnit hext (by omega) hsf]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_markerEnd]
  trfl
  trw [runFast_changedInstance]
  trw [runFast_changedInstance]
  trw [runFast_changedInstance]
  trw [runFast_changedSeg (changed := changed) (va := .ext (.clock clockId))]
  trw [runFast_rememberedValue]
  trw [runFast_ifne_nz]
  side_goals (unfold changedBit; split <;> (try split) <;> rfl)
  trfl
  trw [runFast_initClosure_periodUntil]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_markerEnd]
  trw [runFast_produceState]
  trw [runFast_stateGetValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_endMovableGroup]
  trw [runFast_traceEnd rfl]
  all_goals first
    | (with_unfolding_all rfl)
    | exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `Instant.periodUntil(clock, unit: TimeBased)` on its first composition. -/
theorem periodUntil_1_initialComposition_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 40 ≤ subFuel) (hf : 200 ≤ fuel)
    (start : Int64) (clockId : Nat) (tu : TimeBasedUnit) (changed : UInt32)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
    (hgroups : hp.composer.groups = []) (hstack : hp.composer.groupStack = []) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_periodUntil_1_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)),
          (2, .ext (.timeUnit (.timeBased tu))), (3, .ext .composer), (4, .i32 changed)] hp jh) =
        some (.ext (.period (periodUntilWithUnitTimeModel
          (hp.untilTime start (hp.clockNow hp.clockReads) tu) tu)), endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.clockReads = hp.clockReads + 1 ∧
      endSt.heap.closures = hp.closures.push ("PeriodUntilKt$periodUntil$4$1",
        [.ext (.instant start), .ext (.timeUnit (.timeBased tu)), .ext (.clock clockId)]) ∧
      endSt.heap.composer.stateCells = (hp.composer.nextStateId, .ext (.period (periodUntilWithUnitTimeModel
          (hp.untilTime start (hp.clockNow hp.clockReads) tu) tu))) :: hp.composer.stateCells ∧
      endSt.heap.composer.groupStack = [] := by
  obtain ⟨d1, rfl⟩ : ∃ d1, d = d1 + 1 := ⟨d - 1, by omega⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨⟨ins, groups, gstack, cells, nid, trace⟩, closures, reads, now, untilTz, untilTime⟩ := hp
  dsimp only at hgroups hstack ⊢
  subst hgroups hstack
  apply Exists.intro
  refine ⟨Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl ?_, ?_⟩
  simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntil_1_prog]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  trfl
  trw [runFast_traceStart rfl]
  trfl
  trfl
  trw [runFast_startMovableGroup_fresh]
  trfl
  trfl
  trw [runFast_rememberedValue]
  trw [runFast_getstatic_clean (hc _ _) (by rfl)]
  trfl
  trw [runFast_if_acmpne_fallthrough rfl]
  trw [runFast_clockNow]
  trw [runFast_call_periodUntilWithUnit_1 hext (by omega) hsf]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_markerEnd]
  trfl
  trw [runFast_changedInstance]
  trw [runFast_changedInstance]
  trw [runFast_changedSeg (changed := changed) (va := .ext (.clock clockId))]
  trw [runFast_rememberedValue]
  trw [runFast_ifne_nz]
  side_goals (unfold changedBit; split <;> (try split) <;> rfl)
  trfl
  trw [runFast_initClosure_periodUntil_1]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_markerEnd]
  trw [runFast_produceState]
  trw [runFast_stateGetValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_endMovableGroup]
  trw [runFast_traceEnd rfl]
  all_goals first
    | (with_unfolding_all rfl)
    | exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `Instant.progressivePeriodUntil(clock, unitProgression, timeZone)` on its first composition returns the
progressive model's `(unit, period)` pair for one clock reading. The domain conditions are those of
`periodUntilWithProgressiveUnits_equiv`. -/
theorem progressivePeriodUntil_initialComposition_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 4 ≤ d) (hf : 220 ≤ fuel)
    (start : Int64) (clockId : Nat) (units : List DateTimeUnit) (tz : String) (changed : UInt32)
    (hneUnits : units ≠ []) (hlen31 : units.length < 2 ^ 31) (hfuel : 70 * units.length + 70 ≤ subFuel)
    (hp : TimeHeap)
    (hNotMin : ∀ u ∈ units,
      periodNoAbsMin (periodUntilWithUnitModel (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u) u)
    (listAddr arrAddr : Nat) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray))
    (hgroups : hp.composer.groups = []) (hstack : hp.composer.groupStack = []) :
    let pairs := units.map fun u =>
      (u, periodUntilWithUnitModel (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u)
    ∃ resPair endSt,
      periodUntilWithProgressiveUnitsModel pairs = some resPair ∧
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_progressivePeriodUntil_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)), (2, .heapRef listAddr),
          (3, .ext (.timeZone tz)), (4, .ext .composer), (5, .i32 changed)] hp jh) =
        some (unitPairVal resPair.1 resPair.2, endSt) ∧
      HasTimeStaticsClean endSt.jvmHeap ∧
      endSt.heap.clockReads = hp.clockReads + 1 ∧
      endSt.heap.closures = hp.closures.push ("PeriodUntilKt$progressivePeriodUntil$2$1",
        [.heapRef listAddr, .ext (.clock clockId), .ext (.instant start), .ext (.timeZone tz)]) ∧
      endSt.heap.composer.stateCells =
        (hp.composer.nextStateId, unitPairVal resPair.1 resPair.2) :: hp.composer.stateCells ∧
      endSt.heap.composer.groupStack = [] := by
  obtain ⟨d1, rfl⟩ : ∃ d1, d = d1 + 1 := ⟨d - 1, by omega⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨⟨ins, groups, gstack, cells, nid, trace⟩, closures, reads, now, untilTz, untilTime⟩ := hp
  dsimp only at hgroups hstack hNotMin ⊢
  subst hgroups hstack
  obtain ⟨resPair, jh', hmod, hc', hcall⟩ :=
    runFast_call_periodUntilWithProgressiveUnits hext (d1 := d1) (by omega) (by omega) hneUnits hlen31 hfuel
      (other := now reads)
      (hp := ⟨⟨ins, [⟨(787717454 : UInt32).toInt32, []⟩],
        [⟨(787717454 : UInt32).toInt32, ([] : List JvmVal).length + 1, some ([] : List JvmVal).length⟩],
        cells, nid, trace⟩, closures, reads + 1, now, untilTz, untilTime⟩) hNotMin hc hlist harr
  refine ⟨resPair, ?_⟩
  apply Exists.intro
  refine ⟨hmod, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl ?_, ?_⟩
  simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [PeriodUntilKt_progressivePeriodUntil_prog]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  trfl
  trw [runFast_traceStart rfl]
  trfl
  trfl
  trfl
  trw [runFast_startMovableGroup_fresh]
  trfl
  trfl
  trw [runFast_rememberedValue]
  trw [runFast_getstatic_clean (hc _ _) (by rfl)]
  trfl
  trw [runFast_if_acmpne_fallthrough rfl]
  trw [runFast_clockNow]
  trw [hcall]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_pair]
  trw [runFast_markerEnd]
  trfl
  trw [runFast_changedSeg (changed := changed) (va := .heapRef listAddr)]
  trw [runFast_changedInstance]
  trw [runFast_changedInstance]
  trw [runFast_changedSeg (changed := changed) (va := .ext (.clock clockId))]
  trw [runFast_rememberedValue]
  trw [runFast_ifne_nz]
  side_goals (unfold changedBit; split <;> (try split) <;> (try split) <;> (try split) <;> rfl)
  trfl
  trw [runFast_initClosure_progressivePeriodUntil]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_markerEnd]
  trw [runFast_produceState]
  trw [runFast_stateGetValue]
  trw [runFast_checkcast_pair]
  trw [runFast_endMovableGroup]
  trw [runFast_traceEnd rfl]
  all_goals first
    | (with_unfolding_all rfl)
    | exact ⟨hc', rfl, rfl, rfl, rfl⟩

/-- `Instant.progressivePeriodUntil(clock, unitProgression: List<TimeBased>)` on its first composition. The domain
conditions are those of `periodUntilWithProgressiveUnits_1_equiv`. -/
theorem progressivePeriodUntil_1_initialComposition_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 4 ≤ d) (hf : 220 ≤ fuel)
    (start : Int64) (clockId : Nat) (units : List TimeBasedUnit) (changed : UInt32)
    (hneUnits : units ≠ []) (hlen31 : units.length < 2 ^ 31) (hfuel : 70 * units.length + 70 ≤ subFuel)
    (hp : TimeHeap)
    (hNotMin : ∀ u ∈ units,
      timePeriodNoAbsMin (periodUntilWithUnitTimeModel (hp.untilTime start (hp.clockNow hp.clockReads) u) u) u)
    (listAddr arrAddr : Nat) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray))
    (hgroups : hp.composer.groups = []) (hstack : hp.composer.groupStack = []) :
    let pairs := units.map fun u =>
      (u, periodUntilWithUnitTimeModel (hp.untilTime start (hp.clockNow hp.clockReads) u) u)
    ∃ resPair endSt,
      periodUntilWithProgressiveUnitsTimeModel pairs = some resPair ∧
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_progressivePeriodUntil_1_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)), (2, .heapRef listAddr),
          (3, .ext .composer), (4, .i32 changed)] hp jh) =
        some (unitTimePairVal resPair.1 resPair.2, endSt) ∧
      HasTimeStaticsClean endSt.jvmHeap ∧
      endSt.heap.clockReads = hp.clockReads + 1 ∧
      endSt.heap.closures = hp.closures.push ("PeriodUntilKt$progressivePeriodUntil$4$1",
        [.heapRef listAddr, .ext (.clock clockId), .ext (.instant start)]) ∧
      endSt.heap.composer.stateCells =
        (hp.composer.nextStateId, unitTimePairVal resPair.1 resPair.2) :: hp.composer.stateCells ∧
      endSt.heap.composer.groupStack = [] := by
  obtain ⟨d1, rfl⟩ : ∃ d1, d = d1 + 1 := ⟨d - 1, by omega⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨⟨ins, groups, gstack, cells, nid, trace⟩, closures, reads, now, untilTz, untilTime⟩ := hp
  dsimp only at hgroups hstack hNotMin ⊢
  subst hgroups hstack
  obtain ⟨resPair, jh', hmod, hc', hcall⟩ :=
    runFast_call_periodUntilWithProgressiveUnits_1 hext (d1 := d1) (by omega) (by omega) hneUnits hlen31 hfuel
      (other := now reads)
      (hp := ⟨⟨ins, [⟨(251854803 : UInt32).toInt32, []⟩],
        [⟨(251854803 : UInt32).toInt32, ([] : List JvmVal).length + 1, some ([] : List JvmVal).length⟩],
        cells, nid, trace⟩, closures, reads + 1, now, untilTz, untilTime⟩) hNotMin hc hlist harr
  refine ⟨resPair, ?_⟩
  apply Exists.intro
  refine ⟨hmod, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl ?_, ?_⟩
  simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [PeriodUntilKt_progressivePeriodUntil_1_prog]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  rw [runFast_checkNotNull (by rfl)]
  time_step_blk
  trfl
  trw [runFast_traceStart rfl]
  trfl
  trfl
  trw [runFast_startMovableGroup_fresh]
  trfl
  trfl
  trw [runFast_rememberedValue]
  trw [runFast_getstatic_clean (hc _ _) (by rfl)]
  trfl
  trw [runFast_if_acmpne_fallthrough rfl]
  trw [runFast_clockNow]
  trw [hcall]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_pair]
  trw [runFast_markerEnd]
  trfl
  trw [runFast_changedSeg (changed := changed) (va := .heapRef listAddr)]
  trw [runFast_changedInstance]
  trw [runFast_changedSeg (changed := changed) (va := .ext (.clock clockId))]
  trw [runFast_rememberedValue]
  trw [runFast_ifne_nz]
  side_goals (unfold changedBit; split <;> (try split) <;> (try split) <;> (try split) <;> rfl)
  trfl
  trw [runFast_initClosure_progressivePeriodUntil_1]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_updateRememberedValue]
  trw [runFast_checkcast_ext rfl]
  trw [runFast_markerEnd]
  trw [runFast_produceState]
  trw [runFast_stateGetValue]
  trw [runFast_checkcast_pair]
  trw [runFast_endMovableGroup]
  trw [runFast_traceEnd rfl]
  all_goals first
    | (with_unfolding_all rfl)
    | exact ⟨hc', rfl, rfl, rfl, rfl⟩

end TimeUtil.KotlinJvmVerification
