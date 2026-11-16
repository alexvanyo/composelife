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

/-!
# Lifted programs of the hand-written Kotlin, by call tag

`algKotlinProgLookup` maps the `resolveProg` tag (`algKotlinTag`: `"<short class>.<method>:<descriptor>"`) of
every lifted method of `KotlinJvmBytecode` to its program, for `mkAlgKotlinHooks`. The constructors of the two
function-reference classes are not lifted (they load a class literal) and are not listed.
-/

namespace Algorithm.KotlinJvmVerification
open Algorithm.JvmVerification
open Algorithm.KotlinJvmBytecode

/-- The lifted program of each method of the hand-written Kotlin classes, by `algKotlinTag`. -/
def algKotlinProgLookup (tag : String) : Option (List JvmInstr) :=
  -- BitComputationKt
  if tag = "BitComputationKt.computeNextGen4x4-WZ4Q5Ns:(I)I" then some BitComputationKt_computeNextGen4x4_prog
  else if tag = "BitComputationKt.computeQuadInfo:(I)I" then some BitComputationKt_computeQuadInfo_prog
  else if tag = "BitComputationKt.computeNextGenerationPureKotlin:(J)I" then
    some BitComputationKt_computeNextGenerationPureKotlin_prog
  else if tag = "BitComputationKt.computeNextGenerationPureKotlin-VKZWuLQ:(J)I" then
    some BitComputationKt_computeNextGenerationPureKotlin_1_prog
  else if tag = "BitComputationKt.<clinit>:()V" then some BitComputationKt_clinit_prog
  -- GameOfLifeStepKt
  else if tag = "GameOfLifeStepKt.stepGeneration:(Ljava/util/Set;)Ljava/util/Set;" then some GameOfLifeStepKt_stepGeneration_prog
  else if tag = "GameOfLifeStepKt.stepGenerations:(Ljava/util/Set;I)Ljava/util/Set;" then
    some GameOfLifeStepKt_stepGenerations_prog
  -- HashLifeComputationKt$computeLevel4NextGeneration$1 / $2
  else if tag = "HashLifeComputationKt$computeLevel4NextGeneration$1.invoke-VKZWuLQ:(J)Ljava/lang/Integer;" then
    some HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_prog
  else if tag = "HashLifeComputationKt$computeLevel4NextGeneration$1.invoke:(Ljava/lang/Object;)Ljava/lang/Object;" then
    some HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog
  else if tag = "HashLifeComputationKt$computeLevel4NextGeneration$1.<clinit>:()V" then
    some HashLifeComputationKt_computeLevel4NextGeneration_1_clinit_prog
  else if tag = "HashLifeComputationKt$computeLevel4NextGeneration$2.invoke-VKZWuLQ:(J)Ljava/lang/Integer;" then
    some HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_prog
  else if tag = "HashLifeComputationKt$computeLevel4NextGeneration$2.invoke:(Ljava/lang/Object;)Ljava/lang/Object;" then
    some HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_1_prog
  else if tag = "HashLifeComputationKt$computeLevel4NextGeneration$2.<clinit>:()V" then
    some HashLifeComputationKt_computeLevel4NextGeneration_2_clinit_prog
  -- HashLifeComputationKt
  else if tag = "HashLifeComputationKt.computeNextGeneration-VKZWuLQ:(J)I" then some HashLifeComputationKt_computeNextGeneration_prog
  else if tag = "HashLifeComputationKt.computeNextGeneration:(J)I" then some HashLifeComputationKt_computeNextGeneration_1_prog
  else if tag = "HashLifeComputationKt.packLeafNode:(IIII)J" then some HashLifeComputationKt_packLeafNode_prog
  else if tag = "HashLifeComputationKt.LeafNode:(IIII)J" then some HashLifeComputationKt_LeafNode_prog
  else if tag = "HashLifeComputationKt.getNw-VKZWuLQ:(J)I" then some HashLifeComputationKt_getNw_prog
  else if tag = "HashLifeComputationKt.getNe-VKZWuLQ:(J)I" then some HashLifeComputationKt_getNe_prog
  else if tag = "HashLifeComputationKt.getSw-VKZWuLQ:(J)I" then some HashLifeComputationKt_getSw_prog
  else if tag = "HashLifeComputationKt.getSe-VKZWuLQ:(J)I" then some HashLifeComputationKt_getSe_prog
  else if tag = "HashLifeComputationKt.centeredSubnodeLevel3-VKZWuLQ:(J)I" then some HashLifeComputationKt_centeredSubnodeLevel3_prog
  else if tag = "HashLifeComputationKt.centeredHorizontalSubnodeLevel3-PWzV0Is:(JJ)I" then
    some HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog
  else if tag = "HashLifeComputationKt.centeredVerticalSubnodeLevel3-PWzV0Is:(JJ)I" then
    some HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog
  else if tag = "HashLifeComputationKt.centeredSubSubnodeLevel4-2jIhpxI:(JJJJ)I" then
    some HashLifeComputationKt_centeredSubSubnodeLevel4_prog
  else if tag = "HashLifeComputationKt.centeredSubSubnodeLevel4:(Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;)I" then
    some HashLifeComputationKt_centeredSubSubnodeLevel4_1_prog
  else if tag = "HashLifeComputationKt.computeLevel4NextGeneration-qFGr5tM:(JJJJLkotlin/jvm/functions/Function1;)J" then
    some HashLifeComputationKt_computeLevel4NextGeneration_prog
  else if tag = "HashLifeComputationKt.computeLevel4NextGeneration-qFGr5tM$default:(JJJJLkotlin/jvm/functions/Function1;ILjava/lang/Object;)J" then
    some HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog
  else if tag = "HashLifeComputationKt.computeLevel4NextGeneration:(Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;Lkotlin/jvm/functions/Function1;)J" then
    some HashLifeComputationKt_computeLevel4NextGeneration_1_prog
  else if tag = "HashLifeComputationKt.computeLevel4NextGeneration$default:(Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;Lkotlin/jvm/functions/Function1;ILjava/lang/Object;)J" then
    some HashLifeComputationKt_computeLevel4NextGeneration_default_prog
  -- MacroCellCoordinatesKt
  else if tag = "MacroCellCoordinatesKt.cellToLeafBit:(II)I" then some MacroCellCoordinatesKt_cellToLeafBit_prog
  else if tag = "MacroCellCoordinatesKt.coordinatesToLeaf:(Ljava/util/Set;II)J" then some MacroCellCoordinatesKt_coordinatesToLeaf_prog
  else if tag = "MacroCellCoordinatesKt.coordinatesToLeaf$default:(Ljava/util/Set;IIILjava/lang/Object;)J" then
    some MacroCellCoordinatesKt_coordinatesToLeaf_default_prog
  else if tag = "MacroCellCoordinatesKt.leafToCoordinates:(JII)Ljava/util/Set;" then some MacroCellCoordinatesKt_leafToCoordinates_prog
  else if tag = "MacroCellCoordinatesKt.leafToCoordinates$default:(JIIILjava/lang/Object;)Ljava/util/Set;" then
    some MacroCellCoordinatesKt_leafToCoordinates_default_prog
  else if tag = "MacroCellCoordinatesKt.coordinatesToLevel4:(Ljava/util/Set;II)Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" then
    some MacroCellCoordinatesKt_coordinatesToLevel4_prog
  else if tag = "MacroCellCoordinatesKt.coordinatesToLevel4$default:(Ljava/util/Set;IIILjava/lang/Object;)Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" then
    some MacroCellCoordinatesKt_coordinatesToLevel4_default_prog
  -- CellWindow
  else if tag = "CellWindow.getIntRect:()Landroidx/compose/ui/unit/IntRect;" then some CellWindow_getIntRect_prog
  else if tag = "CellWindow.getTopLeft-nOcc-ac:(Landroidx/compose/ui/unit/IntRect;)J" then some CellWindow_getTopLeft_prog
  else if tag = "CellWindow.getTopRight-nOcc-ac:(Landroidx/compose/ui/unit/IntRect;)J" then some CellWindow_getTopRight_prog
  else if tag = "CellWindow.getBottomRight-nOcc-ac:(Landroidx/compose/ui/unit/IntRect;)J" then
    some CellWindow_getBottomRight_prog
  else if tag = "CellWindow.getBottomLeft-nOcc-ac:(Landroidx/compose/ui/unit/IntRect;)J" then some CellWindow_getBottomLeft_prog
  else if tag = "CellWindow.getCenter-nOcc-ac:(Landroidx/compose/ui/unit/IntRect;)J" then some CellWindow_getCenter_prog
  else if tag = "CellWindow.getTop-impl:(Landroidx/compose/ui/unit/IntRect;)I" then some CellWindow_getTop_impl_prog
  else if tag = "CellWindow.getLeft-impl:(Landroidx/compose/ui/unit/IntRect;)I" then some CellWindow_getLeft_impl_prog
  else if tag = "CellWindow.getBottom-impl:(Landroidx/compose/ui/unit/IntRect;)I" then some CellWindow_getBottom_impl_prog
  else if tag = "CellWindow.getRight-impl:(Landroidx/compose/ui/unit/IntRect;)I" then some CellWindow_getRight_impl_prog
  else if tag = "CellWindow.getWidth-impl:(Landroidx/compose/ui/unit/IntRect;)I" then some CellWindow_getWidth_impl_prog
  else if tag = "CellWindow.getHeight-impl:(Landroidx/compose/ui/unit/IntRect;)I" then some CellWindow_getHeight_impl_prog
  else if tag = "CellWindow.getSize-YbymL2g:(Landroidx/compose/ui/unit/IntRect;)J" then some CellWindow_getSize_prog
  else if tag = "CellWindow.translate-RUbSdm4:(Landroidx/compose/ui/unit/IntRect;J)Landroidx/compose/ui/unit/IntRect;" then
    some CellWindow_translate_prog
  else if tag = "CellWindow.containedPoints-impl:(Landroidx/compose/ui/unit/IntRect;)Ljava/util/List;" then
    some CellWindow_containedPoints_impl_prog
  else if tag = "CellWindow.toString-impl:(Landroidx/compose/ui/unit/IntRect;)Ljava/lang/String;" then
    some CellWindow_toString_impl_prog
  else if tag = "CellWindow.toString:()Ljava/lang/String;" then some CellWindow_toString_prog
  else if tag = "CellWindow.hashCode-impl:(Landroidx/compose/ui/unit/IntRect;)I" then some CellWindow_hashCode_impl_prog
  else if tag = "CellWindow.hashCode:()I" then some CellWindow_hashCode_prog
  else if tag = "CellWindow.equals-impl:(Landroidx/compose/ui/unit/IntRect;Ljava/lang/Object;)Z" then
    some CellWindow_equals_impl_prog
  else if tag = "CellWindow.equals:(Ljava/lang/Object;)Z" then some CellWindow_equals_prog
  else if tag = "CellWindow.<init>:(Landroidx/compose/ui/unit/IntRect;)V" then
    some CellWindow_init_prog
  else if tag = "CellWindow.constructor-impl:(Landroidx/compose/ui/unit/IntRect;)Landroidx/compose/ui/unit/IntRect;" then
    some CellWindow_constructor_impl_prog
  else if tag = "CellWindow.box-impl:(Landroidx/compose/ui/unit/IntRect;)Lcom/alexvanyo/composelife/model/CellWindow;" then
    some CellWindow_box_impl_prog
  else if tag = "CellWindow.unbox-impl:()Landroidx/compose/ui/unit/IntRect;" then some CellWindow_unbox_impl_prog
  else if tag = "CellWindow.equals-impl0:(Landroidx/compose/ui/unit/IntRect;Landroidx/compose/ui/unit/IntRect;)Z" then
    some CellWindow_equals_impl0_prog
  else none

end Algorithm.KotlinJvmVerification
