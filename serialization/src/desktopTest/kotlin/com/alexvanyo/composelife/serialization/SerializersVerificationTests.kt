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

package com.alexvanyo.composelife.serialization

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin serializers in `:serialization` by lifting the live
 * compiled `.class` bytecode from the test runtime classpath into Lean 4 and proving round-trip theorems
 * with `lake env lean`.
 */
class SerializersVerificationTests {
    @Test
    fun bitPackedSerializers_bytecode_roundtrip() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_bitPackedSerializers_roundtrip",
            leanBody = """
                |theorem real_bitPackedSerializers_roundtrip
                |    (self : SerVal) (encId decId : Nat) (v : UInt64) (ox oy : Float32) (r : ClosedFloatRangeModel)
                |    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
                |    (∃ endSt,
                |      Jvm.runJvmRes serBaseHooks 80 Serialization.RealJvmBytecode.IntOffsetSerializer_serialize_prog
                |        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .i64 v)] hp jh) =
                |        some (.unit, endSt) ∧
                |      endSt.heap.encodedLong = some v ∧
                |      ∃ endSt2,
                |        Jvm.runJvmRes serBaseHooks 80 Serialization.RealJvmBytecode.IntOffsetSerializer_deserialize_prog
                |          (initSerJvmState [(0, self), (1, .ext (.decoder decId))]
                |            { hp with decodedLong := v } jh) = some (.i64 v, endSt2)) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes serBaseHooks 80 Serialization.RealJvmBytecode.OffsetSerializer_serialize_prog
                |        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .i64 (packFloats ox oy))] hp jh) =
                |        some (.unit, endSt) ∧
                |      endSt.heap.encodedLong = some (packFloats ox oy) ∧
                |      ∃ endSt2,
                |        Jvm.runJvmRes serBaseHooks 80 Serialization.RealJvmBytecode.OffsetSerializer_deserialize_prog
                |          (initSerJvmState [(0, self), (1, .ext (.decoder decId))]
                |            { hp with decodedLong := packFloats ox oy } jh) = some (.i64 (packFloats ox oy), endSt2)) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes serBaseHooks 50 Serialization.RealJvmBytecode.ClosedFloatRangeSerializer_serialize_prog
                |        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh) =
                |        some (.unit, endSt) ∧
                |      endSt.heap.encodedLong = some (serializeClosedFloatRange r) ∧
                |      ∃ endSt2,
                |        Jvm.runJvmRes serBaseHooks 50 Serialization.RealJvmBytecode.ClosedFloatRangeSerializer_deserialize_prog
                |          (initSerJvmState [(0, self), (1, .ext (.decoder decId))]
                |            { hp with decodedLong := serializeClosedFloatRange r } jh) =
                |          some (.ext (.closedFloatRange r), endSt2)) := by
                |  have h1 : Serialization.RealJvmBytecode.IntOffsetSerializer_serialize_prog =
                |      Serialization.KotlinJvmBytecode.IntOffsetSerializer_serialize_prog := rfl
                |  have h2 : Serialization.RealJvmBytecode.IntOffsetSerializer_deserialize_prog =
                |      Serialization.KotlinJvmBytecode.IntOffsetSerializer_deserialize_prog := rfl
                |  have h3 : Serialization.RealJvmBytecode.OffsetSerializer_serialize_prog =
                |      Serialization.KotlinJvmBytecode.OffsetSerializer_serialize_prog := rfl
                |  have h4 : Serialization.RealJvmBytecode.OffsetSerializer_deserialize_prog =
                |      Serialization.KotlinJvmBytecode.OffsetSerializer_deserialize_prog := rfl
                |  have h5 : Serialization.RealJvmBytecode.ClosedFloatRangeSerializer_serialize_prog =
                |      Serialization.KotlinJvmBytecode.ClosedFloatRangeSerializer_serialize_prog := rfl
                |  have h6 : Serialization.RealJvmBytecode.ClosedFloatRangeSerializer_deserialize_prog =
                |      Serialization.KotlinJvmBytecode.ClosedFloatRangeSerializer_deserialize_prog := rfl
                |  rw [h1, h2, h3, h4, h5, h6]
                |  refine ⟨?_, ?_, ?_⟩
                |  · rcases intOffsetSerializer_serialize_equiv self encId v hp jh with ⟨endSt, hrun, henc⟩
                |    rcases intOffsetSerializer_deserialize_equiv self decId { hp with decodedLong := v } jh with
                |      ⟨endSt2, hrun2, _, _⟩
                |    exact ⟨endSt, hrun, henc, endSt2, hrun2⟩
                |  · rcases offsetSerializer_serialize_equiv self encId ox oy hp jh with ⟨endSt, hrun, henc⟩
                |    rcases offsetSerializer_deserialize_equiv self decId ox oy
                |      { hp with decodedLong := packFloats ox oy } jh rfl with ⟨endSt2, hrun2, _, _⟩
                |    exact ⟨endSt, hrun, henc, endSt2, hrun2⟩
                |  · rcases closedFloatRangeSerializer_serialize_equiv self encId r hp jh with ⟨endSt, hrun, henc⟩
                |    rcases closedFloatRangeSerializer_deserialize_equiv self decId
                |      { hp with decodedLong := serializeClosedFloatRange r } jh with ⟨endSt2, hrun2, _, _⟩
                |    rw [closedFloatRange_roundtrip] at hrun2
                |    exact ⟨endSt, hrun, henc, endSt2, hrun2⟩
            """.trimMargin(),
        )
    }

    @Test
    fun rectAndSurrogatingSerializers_bytecode_roundtrip() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_rectAndSurrogatingSerializers_roundtrip",
            leanBody = """
                |theorem real_rectAndSurrogatingSerializers_roundtrip
                |    (self : SerVal) (encId decId selfAddr surrId fromId toId : Nat)
                |    (serialName descName : String) (r : RectModel) (x : SerPayload)
                |    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
                |    (hstat : HasRectSerializerStatics jh)
                |    (hobj : jh.get? selfAddr =
                |      some (.instance "com/alexvanyo/composelife/serialization/SurrogatingSerializerKt${'$'}SurrogatingSerializer${'$'}1"
                |        [("descriptor", .ext (.serialDescriptor serialName (some descName))),
                |         ("${'$'}convertToSurrogate", .ext (.fn1 toId)),
                |         ("${'$'}convertFromSurrogate", .ext (.fn1 fromId)),
                |         ("${'$'}surrogateSerializer", .ext (.surrogateSer surrId descName))]))
                |    (hinv : hp.fn1Eval fromId (hp.fn1Eval toId x) = x) :
                |    (∃ endSt,
                |      Jvm.runJvmRes serBaseHooks 80 Serialization.RealJvmBytecode.RectSerializer_serialize_prog
                |        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh) =
                |        some (.unit, endSt) ∧
                |      endSt.heap.encodedFloatArray = some (serializeRect r) ∧
                |      ∃ endSt2,
                |        Jvm.runJvmRes serBaseHooks 80 Serialization.RealJvmBytecode.RectSerializer_deserialize_prog
                |          (initSerJvmState [(0, self), (1, .ext (.decoder decId))]
                |            { hp with decodedFloatArray := serializeRect r } jh) =
                |          some (.ext (.rect r), endSt2)) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes serBaseHooks 20
                |        Serialization.RealJvmBytecode.SurrogatingSerializerKt_SurrogatingSerializer_1_serialize_prog
                |        (initSerJvmState [(0, .heapRef selfAddr), (1, .ext (.encoder encId)), (2, .ext (.payload x))] hp jh) =
                |        some (.unit, endSt) ∧
                |      endSt.heap.encodedSurrogate = some (hp.fn1Eval toId x) ∧
                |      Jvm.runJvm serBaseHooks 20
                |        Serialization.RealJvmBytecode.SurrogatingSerializerKt_SurrogatingSerializer_1_deserialize_prog
                |        (initSerJvmState [(0, .heapRef selfAddr), (1, .ext (.decoder decId))]
                |          { hp with decodedSurrogate := hp.fn1Eval toId x } jh) =
                |        some (.ext (.payload x))) := by
                |  have h1 : Serialization.RealJvmBytecode.RectSerializer_serialize_prog =
                |      Serialization.KotlinJvmBytecode.RectSerializer_serialize_prog := rfl
                |  have h2 : Serialization.RealJvmBytecode.RectSerializer_deserialize_prog =
                |      Serialization.KotlinJvmBytecode.RectSerializer_deserialize_prog := rfl
                |  have h3 : Serialization.RealJvmBytecode.SurrogatingSerializerKt_SurrogatingSerializer_1_serialize_prog =
                |      Serialization.KotlinJvmBytecode.SurrogatingSerializerKt_SurrogatingSerializer_1_serialize_prog := rfl
                |  have h4 : Serialization.RealJvmBytecode.SurrogatingSerializerKt_SurrogatingSerializer_1_deserialize_prog =
                |      Serialization.KotlinJvmBytecode.SurrogatingSerializerKt_SurrogatingSerializer_1_deserialize_prog := rfl
                |  rw [h1, h2, h3, h4]
                |  refine ⟨?_, ?_⟩
                |  · rcases rectSerializer_serialize_equiv self encId r hp jh hstat with ⟨endSt, hrun, henc⟩
                |    refine ⟨endSt, hrun, henc, ?_⟩
                |    cases r with
                |    | mk l t ri b =>
                |      exact rectSerializer_deserialize_equiv self decId l t ri b
                |        { hp with decodedFloatArray := serializeRect ⟨l, t, ri, b⟩ } jh hstat rfl
                |  · rcases surrogatingSerializer_serialize_equiv selfAddr surrId fromId toId encId
                |      serialName descName x hp jh hobj with ⟨endSt, hrun, henc⟩
                |    refine ⟨endSt, hrun, henc, ?_⟩
                |    rw [surrogatingSerializer_deserialize_equiv selfAddr surrId fromId toId decId
                |      serialName descName { hp with decodedSurrogate := hp.fn1Eval toId x } jh hobj]
                |    simp [hinv]
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "serialization",
            classResourcePath = "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/serialization/IntOffsetSerializer.class",
                "com/alexvanyo/composelife/serialization/OffsetSerializer.class",
                "com/alexvanyo/composelife/serialization/RectSerializer.class",
                "com/alexvanyo/composelife/serialization/SurrogatingSerializerKt\$SurrogatingSerializer\$1.class",
            ),
            realBytecodeNamespace = "Serialization.RealJvmBytecode",
            instrType = "Serialization.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "ClosedFloatRangeSerializer_serialize_prog",
                "ClosedFloatRangeSerializer_deserialize_prog",
                "IntOffsetSerializer_serialize_prog",
                "IntOffsetSerializer_deserialize_prog",
                "OffsetSerializer_serialize_prog",
                "OffsetSerializer_deserialize_prog",
                "RectSerializer_serialize_prog",
                "RectSerializer_deserialize_prog",
                "SurrogatingSerializerKt_SurrogatingSerializer_1_serialize_prog",
                "SurrogatingSerializerKt_SurrogatingSerializer_1_deserialize_prog",
            ),
            defaultImports = listOf(
                "Jvm.Semantics",
                "JvmSemantics",
                "KotlinJvmBytecode",
                "models.SerializersModel",
                "theorems.SerializersModelTheorems",
                "proofs.KotlinJvmEquiv.Serializers",
            ),
            defaultOpens = listOf(
                "Serialization.JvmVerification",
                "Serialization.Model",
                "Serialization.KotlinJvmVerification",
            ),
        )
    }
}
