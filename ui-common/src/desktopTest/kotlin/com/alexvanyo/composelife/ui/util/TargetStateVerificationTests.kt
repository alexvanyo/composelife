/*
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
 */

package com.alexvanyo.composelife.ui.util

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin code in `TargetState.kt` by lifting the actual compiled
 * `TargetState$InProgress.class` and `TargetStateKt.class` JVM bytecode from the test runtime classpath into Lean 4
 * and proving theorems about that real bytecode with `lake env lean`.
 */
class TargetStateVerificationTests {
    @Test
    fun inProgress_accessors_and_components_bytecode_read_fields() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_inProgress_accessors_read_fields",
            leanBody = """
                |theorem real_inProgress_accessors_read_fields
                |    (resolveProg : String → Option (List JvmInstr)) (depth sf fuel : Nat) (hf : 5 ≤ fuel)
                |    (jh : Jvm.JvmHeap UiExt) (addr : Nat) (c p : JvmVal) (pr : Float32) (m : JvmVal)
                |    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_getCurrent_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (c, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_getProvisional_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (p, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_getProgress_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (.f32 pr, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_getMetadata_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (m, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_component1_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (c, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_component2_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (p, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_component3_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (.f32 pr, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
                |        UiCommon.RealJvmBytecode.TargetState_InProgress_component4_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |      some (m, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) := by
                |  have h1 : UiCommon.RealJvmBytecode.TargetState_InProgress_getCurrent_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_getCurrent_prog := rfl
                |  have h2 : UiCommon.RealJvmBytecode.TargetState_InProgress_getProvisional_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_getProvisional_prog := rfl
                |  have h3 : UiCommon.RealJvmBytecode.TargetState_InProgress_getProgress_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_getProgress_prog := rfl
                |  have h4 : UiCommon.RealJvmBytecode.TargetState_InProgress_getMetadata_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_getMetadata_prog := rfl
                |  have h5 : UiCommon.RealJvmBytecode.TargetState_InProgress_component1_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_component1_prog := rfl
                |  have h6 : UiCommon.RealJvmBytecode.TargetState_InProgress_component2_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_component2_prog := rfl
                |  have h7 : UiCommon.RealJvmBytecode.TargetState_InProgress_component3_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_component3_prog := rfl
                |  have h8 : UiCommon.RealJvmBytecode.TargetState_InProgress_component4_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_component4_prog := rfl
                |  rw [h1, h2, h3, h4, h5, h6, h7, h8]
                |  exact ⟨getCurrent_equiv resolveProg depth sf fuel hf hi hp,
                |    getProvisional_equiv resolveProg depth sf fuel hf hi hp,
                |    getProgress_equiv resolveProg depth sf fuel hf hi hp,
                |    getMetadata_equiv resolveProg depth sf fuel hf hi hp,
                |    component1_equiv resolveProg depth sf fuel hf hi hp,
                |    component2_equiv resolveProg depth sf fuel hf hi hp,
                |    component3_equiv resolveProg depth sf fuel hf hi hp,
                |    component4_equiv resolveProg depth sf fuel hf hi hp⟩
            """.trimMargin(),
        )
    }

    @Test
    fun inProgress_constructor_and_companion_bytecode_enforce_invariant() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_inProgress_constructor_enforces_invariant",
            leanBody = """
                |theorem real_inProgress_constructor_enforces_invariant
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsUiProgs resolveProg)
                |    (d sf fuel : Nat) (hsf : 5 ≤ sf) (hf : 45 ≤ fuel)
                |    (jh : Jvm.JvmHeap UiExt) (addr : Nat) (cls : String) (fields : List (String × JvmVal))
                |    (hget : jh.get? addr = some (.instance cls fields))
                |    (hcls : cls = "com/alexvanyo/composelife/ui/util/TargetState${'$'}InProgress" ∨
                |      cls = "TargetState${'$'}InProgress")
                |    (c p : JvmVal) (pr : Float32) (m : JvmVal) (hp : UiHeap)
                |    (hcm : c.equalsModeled jh = true) (hpm : p.equalsModeled jh = true) :
                |    (Jvm.JvmVal.beqVal beqUiExt c p = false →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
                |            UiCommon.RealJvmBytecode.TargetState_InProgress_init_prog
                |            (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
                |          some (.unit, st') ∧
                |        HasInProgressFields st'.jvmHeap addr c p pr m ∧ st'.heap = hp) ∧
                |    (Jvm.JvmVal.beqVal beqUiExt c p = true →
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
                |          UiCommon.RealJvmBytecode.TargetState_InProgress_init_prog
                |          (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
                |        none) ∧
                |    ∃ st',
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel
                |          UiCommon.RealJvmBytecode.TargetState_InProgress_clinit_prog (initUiJvmState [] hp jh) =
                |        some (.unit, st') ∧
                |      st'.jvmHeap.getStatic? "com/alexvanyo/composelife/ui/util/TargetState${'$'}InProgress" "Companion" =
                |        some (.ext (.companion "TargetState${'$'}InProgress${'$'}Companion")) := by
                |  have hC : UiCommon.RealJvmBytecode.TargetState_InProgress_init_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_init_prog := rfl
                |  have hI : UiCommon.RealJvmBytecode.TargetState_InProgress_clinit_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_clinit_prog := rfl
                |  rw [hC, hI]
                |  exact ⟨fun hne => inProgress_ctor_valid_equiv resolveProg d sf fuel hext hsf hf jh addr cls fields
                |      hget hcls c p pr m hp hne hcm hpm,
                |    fun heq => inProgress_ctor_trap_equiv resolveProg d sf fuel hext hsf hf jh addr cls fields
                |      hget hcls c p pr m hp heq hcm hpm,
                |    clinit_TargetState_InProgress_equiv resolveProg d sf fuel (by omega) hp jh⟩
            """.trimMargin(),
        )
    }

    @Test
    fun inProgress_copy_bytecode_enforces_invariant() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_inProgress_copy_enforces_invariant",
            leanBody = """
                |theorem real_inProgress_copy_enforces_invariant
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsUiProgs resolveProg)
                |    (d sf fuel : Nat) (hsf : 45 ≤ sf) (hf : 36 ≤ fuel)
                |    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (thisVal c p : JvmVal) (pr : Float32) (m : JvmVal)
                |    (addr : Nat) (cOld pOld : JvmVal) (prOld : Float32) (mOld : JvmVal)
                |    (hi : HasInProgressFields jh addr cOld pOld prOld mOld) (mask : UInt32) (handler : JvmVal)
                |    (hcm : c.equalsModeled jh = true) (hpm : p.equalsModeled jh = true)
                |    (hcm' : (if (mask &&& 1) == 0 then c else cOld).equalsModeled jh = true)
                |    (hpm' : (if (mask &&& 2) == 0 then p else pOld).equalsModeled jh = true) :
                |    (Jvm.JvmVal.beqVal beqUiExt c p = false →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) fuel UiCommon.RealJvmBytecode.TargetState_InProgress_copy_prog
                |            (initUiJvmState [(0, thisVal), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
                |          some (.heapRef jh.objects.size, st') ∧
                |        HasInProgressFields st'.jvmHeap jh.objects.size c p pr m ∧ st'.heap = hp) ∧
                |    (Jvm.JvmVal.beqVal beqUiExt c p = true →
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) fuel UiCommon.RealJvmBytecode.TargetState_InProgress_copy_prog
                |          (initUiJvmState [(0, thisVal), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) = none) ∧
                |    (Jvm.JvmVal.beqVal beqUiExt
                |        (if (mask &&& 1) == 0 then c else cOld) (if (mask &&& 2) == 0 then p else pOld) = false →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) fuel
                |            UiCommon.RealJvmBytecode.TargetState_InProgress_copy_default_prog
                |            (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m),
                |              (5, .i32 mask), (6, handler)] hp jh) =
                |          some (.heapRef jh.objects.size, st') ∧
                |        HasInProgressFields st'.jvmHeap jh.objects.size
                |          (if (mask &&& 1) == 0 then c else cOld) (if (mask &&& 2) == 0 then p else pOld)
                |          (if (mask &&& 4) == 0 then pr else prOld) (if (mask &&& 8) == 0 then m else mOld) ∧
                |        st'.heap = hp) ∧
                |    (Jvm.JvmVal.beqVal beqUiExt
                |        (if (mask &&& 1) == 0 then c else cOld) (if (mask &&& 2) == 0 then p else pOld) = true →
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) fuel
                |          UiCommon.RealJvmBytecode.TargetState_InProgress_copy_default_prog
                |          (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m),
                |            (5, .i32 mask), (6, handler)] hp jh) = none) := by
                |  have hC : UiCommon.RealJvmBytecode.TargetState_InProgress_copy_prog = UiCommon.KotlinJvmBytecode.TargetState_InProgress_copy_prog := rfl
                |  have hD : UiCommon.RealJvmBytecode.TargetState_InProgress_copy_default_prog =
                |      UiCommon.KotlinJvmBytecode.TargetState_InProgress_copy_default_prog := rfl
                |  rw [hC, hD]
                |  exact ⟨fun hne => copy_valid_equiv resolveProg d sf fuel hext hsf (by omega)
                |      thisVal c p pr m jh hp hne hcm hpm,
                |    fun heq => copy_trap_equiv resolveProg d sf fuel hext hsf (by omega)
                |      thisVal c p pr m jh hp heq hcm hpm,
                |    fun hne => copy_default_valid_equiv resolveProg d sf fuel hext hsf hf hi
                |      c p pr m mask handler hp hne hcm' hpm',
                |    fun heq => copy_default_trap_equiv resolveProg d sf fuel hext hsf hf hi
                |      c p pr m mask handler hp heq hcm' hpm'⟩
            """.trimMargin(),
        )
    }

    @Test
    fun inProgress_object_methods_bytecode_implement_data_class_semantics() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_inProgress_object_methods",
            leanBody = """
                |theorem real_inProgress_object_methods
                |    (resolveProg : String → Option (List JvmInstr)) (depth sf : Nat)
                |    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (addr1 addr2 : Nat) (hne : addr1 ≠ addr2)
                |    (c1 p1 c2 p2 m1 m2 : JvmVal) (pr1 pr2 : Float32)
                |    (hi1 : HasInProgressFields jh addr1 c1 p1 pr1 m1)
                |    (hi2 : HasInProgressFields jh addr2 c2 p2 pr2 m2)
                |    (hmod : [c1, p1, m1, c2, p2, m2].all (·.equalsModeled jh) = true) :
                |    (∀ hc hpv hm : UInt32,
                |      uiNullableHashCode c1 = some hc → uiNullableHashCode p1 = some hpv →
                |      uiNullableHashCode m1 = some hm →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) 45 UiCommon.RealJvmBytecode.TargetState_InProgress_hashCode_prog
                |            (initUiJvmState [(0, .heapRef addr1)] hp jh) =
                |          some (.i32 ((((hc * 31 + hpv) * 31 + floatHashCode pr1) * 31) + hm), st') ∧
                |        st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st',
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) 48 UiCommon.RealJvmBytecode.TargetState_InProgress_equals_prog
                |          (initUiJvmState [(0, .heapRef addr1), (1, .heapRef addr1)] hp jh) =
                |        some (.i32 1, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st',
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) 48 UiCommon.RealJvmBytecode.TargetState_InProgress_equals_prog
                |          (initUiJvmState [(0, .heapRef addr1), (1, .null)] hp jh) =
                |        some (.i32 0, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∀ c, HasSingleFields jh addr2 c →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) 48 UiCommon.RealJvmBytecode.TargetState_InProgress_equals_prog
                |            (initUiJvmState [(0, .heapRef addr1), (1, .heapRef addr2)] hp jh) =
                |          some (.i32 0, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st',
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) 48 UiCommon.RealJvmBytecode.TargetState_InProgress_equals_prog
                |          (initUiJvmState [(0, .heapRef addr1), (1, .heapRef addr2)] hp jh) =
                |        some (.i32 (if Jvm.JvmVal.beqVal beqUiExt c1 c2 && Jvm.JvmVal.beqVal beqUiExt p1 p2 &&
                |            (Model.floatCompare pr1 pr2 == 0) && Jvm.JvmVal.beqVal beqUiExt m1 m2 then 1 else 0),
                |          st') ∧
                |      st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) 48 UiCommon.RealJvmBytecode.TargetState_InProgress_toString_prog
                |        (initUiJvmState [(0, .heapRef addr1)] hp jh) = none := by
                |  have hH : UiCommon.RealJvmBytecode.TargetState_InProgress_hashCode_prog = UiCommon.KotlinJvmBytecode.TargetState_InProgress_hashCode_prog := rfl
                |  have hE : UiCommon.RealJvmBytecode.TargetState_InProgress_equals_prog = UiCommon.KotlinJvmBytecode.TargetState_InProgress_equals_prog := rfl
                |  have hT : UiCommon.RealJvmBytecode.TargetState_InProgress_toString_prog = UiCommon.KotlinJvmBytecode.TargetState_InProgress_toString_prog := rfl
                |  rw [hH, hE, hT]
                |  exact ⟨fun _ _ _ hhc hhp hhm =>
                |      hashCode_equiv resolveProg depth sf 45 (Nat.le_refl _) hi1 hp hhc hhp hhm,
                |    equals_sameRef_equiv resolveProg depth sf 48 (by omega) addr1 jh hp,
                |    equals_null_equiv resolveProg depth sf 48 (by omega) addr1 jh hp,
                |    fun _ hs => equals_single_equiv resolveProg depth sf 48 (by omega) hne hs hp,
                |    equals_inProgress_equiv resolveProg depth sf 48 (Nat.le_refl _) hne hi1 hi2 hp hmod,
                |    toString_halts_equiv resolveProg depth sf 48 (by omega) hi1 hp⟩
            """.trimMargin(),
        )
    }

    @Test
    fun isInProgress_and_progressToTrue_bytecode_implement_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_isInProgress_progressToTrue_implement_model",
            leanBody = """
                |theorem real_isInProgress_progressToTrue_implement_model
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsUiProgs resolveProg)
                |    (d sf fuel : Nat) (hsf : 5 ≤ sf) (hf : 21 ≤ fuel)
                |    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (addr : Nat) :
                |    (∀ c, HasSingleFields jh addr c →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel
                |            UiCommon.RealJvmBytecode.TargetStateKt_isInProgress_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |          some (.i32 (if (TargetState.single c : TargetState JvmVal Unit).isInProgress then 1 else 0),
                |            st') ∧
                |        st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∀ c p pr m, HasInProgressFields jh addr c p pr m →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel
                |            UiCommon.RealJvmBytecode.TargetStateKt_isInProgress_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |          some (.i32 (if (TargetState.inProgress c p pr m : TargetState JvmVal JvmVal).isInProgress
                |            then 1 else 0), st') ∧
                |        st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∀ cb : Bool, HasSingleFields jh addr (.boxedBool cb) →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
                |            UiCommon.RealJvmBytecode.TargetStateKt_getProgressToTrue_prog
                |            (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |          some (.f32 (TargetState.single cb : TargetState Bool Unit).progressToTrue, st') ∧
                |        st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∀ (cb pb : Bool) (pr : Float32) (m : JvmVal),
                |      HasInProgressFields jh addr (.boxedBool cb) (.boxedBool pb) pr m →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
                |            UiCommon.RealJvmBytecode.TargetStateKt_getProgressToTrue_prog
                |            (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |          some (.f32 (TargetState.inProgress cb pb pr () : TargetState Bool Unit).progressToTrue,
                |            st') ∧
                |        st'.jvmHeap = jh ∧ st'.heap = hp) := by
                |  have hI : UiCommon.RealJvmBytecode.TargetStateKt_isInProgress_prog =
                |      UiCommon.KotlinJvmBytecode.TargetStateKt_isInProgress_prog := rfl
                |  have hP : UiCommon.RealJvmBytecode.TargetStateKt_getProgressToTrue_prog =
                |      UiCommon.KotlinJvmBytecode.TargetStateKt_getProgressToTrue_prog := rfl
                |  rw [hI, hP]
                |  refine ⟨fun c hs => ?_, fun c p pr m hi => ?_,
                |    fun cb hs => getProgressToTrue_single_equiv resolveProg (d + 1) sf fuel (by omega) hs hp,
                |    fun cb pb pr m hi => getProgressToTrue_inProgress_equiv resolveProg d sf fuel hext hsf hf
                |      (cb := cb) hi hp⟩
                |  · obtain ⟨st', hrun, hmodel, hj, hh⟩ :=
                |      isInProgress_single_equiv resolveProg d sf fuel (by omega) hs hp
                |    exact ⟨st', by rw [hmodel]; exact hrun, hj, hh⟩
                |  · obtain ⟨st', hrun, hmodel, hj, hh⟩ :=
                |      isInProgress_inProgress_equiv resolveProg d sf fuel (by omega) hi hp
                |    exact ⟨st', by rw [hmodel]; exact hrun, hj, hh⟩
            """.trimMargin(),
        )
    }

    @Test
    fun boolean_operators_bytecode_implement_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_boolean_operators_implement_model",
            leanBody = """
                |theorem real_boolean_operators_implement_model
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsUiProgs resolveProg)
                |    (d sf : Nat) (hsf : 45 ≤ sf)
                |    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (addr : Nat)
                |    (hstat :
                |      jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt${'$'}not${'$'}1" "INSTANCE" =
                |        none ∨
                |      jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt${'$'}not${'$'}1" "INSTANCE" =
                |        some (.ext .notLambda)) :
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) 14 UiCommon.RealJvmBytecode.TargetStateKt_and_prog
                |        (initUiJvmState [(0, .heapRef addr), (1, .bool true)] hp jh) =
                |      some (.heapRef addr, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) 14 UiCommon.RealJvmBytecode.TargetStateKt_and_prog
                |        (initUiJvmState [(0, .heapRef addr), (1, .bool false)] hp jh) =
                |      some (.heapRef jh.objects.size, st') ∧
                |      HasSingleFields st'.jvmHeap jh.objects.size (.boxedBool false) ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) 14 UiCommon.RealJvmBytecode.TargetStateKt_or_prog
                |        (initUiJvmState [(0, .heapRef addr), (1, .bool true)] hp jh) =
                |      some (.heapRef jh.objects.size, st') ∧
                |      HasSingleFields st'.jvmHeap jh.objects.size (.boxedBool true) ∧ st'.heap = hp) ∧
                |    (∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) 14 UiCommon.RealJvmBytecode.TargetStateKt_or_prog
                |        (initUiJvmState [(0, .heapRef addr), (1, .bool false)] hp jh) =
                |      some (.heapRef addr, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp) ∧
                |    (∀ cb : Bool, HasSingleFields jh addr (.boxedBool cb) →
                |      ∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) 8 UiCommon.RealJvmBytecode.TargetStateKt_not_prog
                |          (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |        some (.heapRef jh.objects.size, st') ∧
                |        HasSingleFields st'.jvmHeap jh.objects.size (.boxedBool (!cb)) ∧ st'.heap = hp) ∧
                |    (∀ (cb pb : Bool) (pr : Float32) (m : JvmVal),
                |      HasInProgressFields jh addr (.boxedBool cb) (.boxedBool pb) pr m → cb ≠ pb →
                |      ∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) 8 UiCommon.RealJvmBytecode.TargetStateKt_not_prog
                |          (initUiJvmState [(0, .heapRef addr)] hp jh) =
                |        some (.heapRef jh.objects.size, st') ∧
                |        HasInProgressFields st'.jvmHeap jh.objects.size (.boxedBool (!cb)) (.boxedBool (!pb)) pr m ∧
                |        st'.heap = hp) := by
                |  have hA : UiCommon.RealJvmBytecode.TargetStateKt_and_prog = UiCommon.KotlinJvmBytecode.TargetStateKt_and_prog := rfl
                |  have hO : UiCommon.RealJvmBytecode.TargetStateKt_or_prog = UiCommon.KotlinJvmBytecode.TargetStateKt_or_prog := rfl
                |  have hN : UiCommon.RealJvmBytecode.TargetStateKt_not_prog = UiCommon.KotlinJvmBytecode.TargetStateKt_not_prog := rfl
                |  rw [hA, hO, hN]
                |  exact ⟨and_true_equiv resolveProg d sf 14 (by omega) addr jh hp,
                |    and_false_equiv resolveProg d sf 14 (by omega) addr jh hp,
                |    or_true_equiv resolveProg d sf 14 (by omega) addr jh hp,
                |    or_false_equiv resolveProg d sf 14 (by omega) addr jh hp,
                |    fun _ hs => not_single_equiv resolveProg d sf 8 hext (by omega) (Nat.le_refl _) hs hp hstat,
                |    fun _ _ _ _ hi hne => not_inProgress_equiv resolveProg d sf 8 hext hsf (Nat.le_refl _) hi hne hp
                |      hstat⟩
            """.trimMargin(),
        )
    }

    @Test
    fun map_bytecode_implements_checked_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_map_implements_checked_model",
            leanBody = """
                |theorem real_map_implements_checked_model
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsUiProgs resolveProg)
                |    (d sf : Nat) (hsf : 45 ≤ sf)
                |    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (addr : Nat)
                |    (fnVal : JvmVal) (f : JvmVal → Option JvmVal) (hfn : HasFn1Behavior hp fnVal f) :
                |    (∀ c c', HasSingleFields jh addr c → c.isCat2 = false → f c = some c' →
                |      ∃ st',
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) 38 UiCommon.RealJvmBytecode.TargetStateKt_map_prog
                |            (initUiJvmState [(0, .heapRef addr), (1, fnVal)] hp jh) =
                |          some (.heapRef jh.objects.size, st') ∧
                |        HasSingleFields st'.jvmHeap jh.objects.size c' ∧ st'.heap = hp) ∧
                |    (∀ c p pr m c' p', HasInProgressFields jh addr c p pr m → c.isCat2 = false → p.isCat2 = false →
                |      f c = some c' → f p = some p' →
                |      c'.equalsModeled jh = true → p'.equalsModeled jh = true →
                |      (Jvm.JvmVal.beqVal beqUiExt c' p' = false →
                |        ∃ st',
                |          Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) 38 UiCommon.RealJvmBytecode.TargetStateKt_map_prog
                |              (initUiJvmState [(0, .heapRef addr), (1, fnVal)] hp jh) =
                |            some (.heapRef jh.objects.size, st') ∧
                |          HasInProgressFields st'.jvmHeap jh.objects.size c' p' pr m ∧ st'.heap = hp) ∧
                |      (Jvm.JvmVal.beqVal beqUiExt c' p' = true →
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) 38 UiCommon.RealJvmBytecode.TargetStateKt_map_prog
                |            (initUiJvmState [(0, .heapRef addr), (1, fnVal)] hp jh) = none)) := by
                |  have hM : UiCommon.RealJvmBytecode.TargetStateKt_map_prog = UiCommon.KotlinJvmBytecode.TargetStateKt_map_prog := rfl
                |  rw [hM]
                |  exact ⟨fun _ _ hs hc hfc => map_single_equiv resolveProg (d + 2) sf 38 (by omega) hs hc hp hfn hfc,
                |    fun _ _ _ _ _ _ hi hc hpv hfc hfp hcm hpm =>
                |      ⟨fun hne => map_inProgress_valid_equiv resolveProg d sf 38 hext hsf (Nat.le_refl _) hi hc hpv hp
                |        hfn hfc hfp hne hcm hpm,
                |      fun heq => map_inProgress_trap_equiv resolveProg d sf 38 hext hsf (Nat.le_refl _) hi hc hpv hp
                |        hfn hfc hfp heq hcm hpm⟩⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "ui-common",
            classResourcePath = "com/alexvanyo/composelife/ui/util/TargetState\$InProgress.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/ui/util/TargetStateKt.class",
            ),
            realBytecodeNamespace = "UiCommon.RealJvmBytecode",
            instrType = "UiCommon.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "TargetState_InProgress_init_prog",
                "TargetState_InProgress_getCurrent_prog",
                "TargetState_InProgress_getProvisional_prog",
                "TargetState_InProgress_getProgress_prog",
                "TargetState_InProgress_getMetadata_prog",
                "TargetState_InProgress_component1_prog",
                "TargetState_InProgress_component2_prog",
                "TargetState_InProgress_component3_prog",
                "TargetState_InProgress_component4_prog",
                "TargetState_InProgress_copy_prog",
                "TargetState_InProgress_copy_default_prog",
                "TargetState_InProgress_toString_prog",
                "TargetState_InProgress_hashCode_prog",
                "TargetState_InProgress_equals_prog",
                "TargetState_InProgress_clinit_prog",
                "TargetStateKt_isInProgress_prog",
                "TargetStateKt_getProgressToTrue_prog",
                "TargetStateKt_not_prog",
                "TargetStateKt_and_prog",
                "TargetStateKt_or_prog",
                "TargetStateKt_map_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.TargetStateModel",
                "theorems.TargetStateModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.TargetState",
            ),
            defaultOpens = listOf(
                "UiCommon",
                "UiCommon.JvmVerification",
                "UiCommon.Model",
                "UiCommon.KotlinJvmVerification",
            ),
        )
    }
}
