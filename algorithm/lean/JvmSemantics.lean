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

import Init.Data.UInt
import Jvm
import Algorithm.Basic
import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.MacroCellHash
import Algorithm.HashLife
import Algorithm.FlatHashLife
import Algorithm.SerialCore
import Algorithm.Life105
import Algorithm.Life106
import Algorithm.Plaintext
import Algorithm.RLE

namespace Algorithm.JvmVerification

export Jvm (JvmInstr setLocal coerceInI32 nlz32)

inductive ArenaU32Field where
  | l4Buckets | l4Next
  | cellNw | cellNe | cellSw | cellSe | cellStepRes | cellBuckets | cellNext
  | remapL4 | remapCell
  deriving DecidableEq, Repr, Inhabited

inductive ArenaU64Field where
  | l4Nw | l4Ne | l4Sw | l4Se | l4StepRes | cellPop
  deriving DecidableEq, Repr, Inhabited

inductive ArenaU8Field where
  | l4HasRes | cellLevel
  deriving DecidableEq, Repr, Inhabited

inductive AlgExt where
  | mc (m : Algorithm.MacroCell)
  | stepPrep (p : Algorithm.StepPreparation)
  | stepQuad (q : Algorithm.StepQuadrants)
  | hlState (s : Algorithm.HashLifeStepState)
  | pruneThresh (p : Algorithm.PruneThresholds)
  | stepBatch (b : Algorithm.StepBatchResult)
  | rleStatus (s : Algorithm.RLEStatus)
  | arenaRef (id : Nat)
  | arenaU32Ref (id : Nat) (field : ArenaU32Field)
  | arenaU64Ref (id : Nat) (field : ArenaU64Field)
  | arenaU8Ref (id : Nat) (field : ArenaU8Field)
  | u64Ref (id : Nat)
  | asciiRef (id : Nat)
  | byteArr (b : ByteArray)
  | u32Arr (xs : Array UInt32)
  | strGrowBuf (b : Algorithm.GrowBuf String)
  | rleWarnGrowBuf (b : Algorithm.GrowBuf Algorithm.RLEWarning)
  | mcWarnGrowBuf (b : Algorithm.GrowBuf Algorithm.MacrocellWarning)
  | ptWarnGrowBuf (b : Algorithm.GrowBuf Algorithm.PlaintextWarning)
  | u64GrowBuf (b : Algorithm.GrowBuf UInt64)
  | boolGrowBuf (b : Algorithm.GrowBuf Bool)
  | mcGrowBuf (b : Algorithm.GrowBuf Algorithm.MacroCell)
  | u32PairGrowBuf (b : Algorithm.GrowBuf (UInt32 × UInt32))
  | u8U32PairGrowBuf (b : Algorithm.GrowBuf (UInt8 × UInt32))
  | dagWriter (w : Algorithm.DagWriter)
  | cellFrames (fs : List Algorithm.CellFrame)
  | fnU64ToU32 (f : UInt64 → UInt32)
  | fnMcToU64 (f : Algorithm.MacroCell → UInt64)
  | fnMcToMc (f : Algorithm.MacroCell → Algorithm.MacroCell)
  | fnMcToOptMc (f : Algorithm.MacroCell → Option Algorithm.MacroCell)
  | fnHlToHl (f : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState)
  deriving Inhabited

structure AlgHeap where
  arenas : List Algorithm.FlatHashLifeArena := []
  u64Arrays : List (Array UInt64) := []
  asciiArrays : List Algorithm.AsciiBytes := []

abbrev JvmVal := Jvm.JvmVal AlgExt

abbrev JvmState := Jvm.JvmState AlgExt AlgHeap

namespace JvmVal
export Jvm.JvmVal (
  i32 i64 f64 bool null unit uninit str allocRef
  boxedByte boxedUByte boxedInt boxedUInt boxedLong boxedULong
  pair strArr ext
)
end JvmVal

def initJvmState (slots : List (Nat × JvmVal))
    (arenas : List Algorithm.FlatHashLifeArena := [])
    (u64Arrays : List (Array UInt64) := [])
    (asciiArrays : List Algorithm.AsciiBytes := []) : JvmState :=
  Jvm.initJvmState slots (.i32 0) ⟨arenas, u64Arrays, asciiArrays⟩

def getArenaU32 (a : Algorithm.FlatHashLifeArena) : ArenaU32Field → Array UInt32
  | .l4Buckets => a.l4Buckets
  | .l4Next => a.l4Next
  | .cellNw => a.cellNw
  | .cellNe => a.cellNe
  | .cellSw => a.cellSw
  | .cellSe => a.cellSe
  | .cellStepRes => a.cellStepRes
  | .cellBuckets => a.cellBuckets
  | .cellNext => a.cellNext
  | .remapL4 => a.remapL4
  | .remapCell => a.remapCell

def setArenaU32 (a : Algorithm.FlatHashLifeArena) (f : ArenaU32Field) (arr : Array UInt32) :
    Algorithm.FlatHashLifeArena :=
  match f with
  | .l4Buckets => { a with l4Buckets := arr }
  | .l4Next => { a with l4Next := arr }
  | .cellNw => { a with cellNw := arr }
  | .cellNe => { a with cellNe := arr }
  | .cellSw => { a with cellSw := arr }
  | .cellSe => { a with cellSe := arr }
  | .cellStepRes => { a with cellStepRes := arr }
  | .cellBuckets => { a with cellBuckets := arr }
  | .cellNext => { a with cellNext := arr }
  | .remapL4 => { a with remapL4 := arr }
  | .remapCell => { a with remapCell := arr }

def getArenaU64 (a : Algorithm.FlatHashLifeArena) : ArenaU64Field → Array UInt64
  | .l4Nw => a.l4Nw
  | .l4Ne => a.l4Ne
  | .l4Sw => a.l4Sw
  | .l4Se => a.l4Se
  | .l4StepRes => a.l4StepRes
  | .cellPop => a.cellPop

def setArenaU64 (a : Algorithm.FlatHashLifeArena) (f : ArenaU64Field) (arr : Array UInt64) :
    Algorithm.FlatHashLifeArena :=
  match f with
  | .l4Nw => { a with l4Nw := arr }
  | .l4Ne => { a with l4Ne := arr }
  | .l4Sw => { a with l4Sw := arr }
  | .l4Se => { a with l4Se := arr }
  | .l4StepRes => { a with l4StepRes := arr }
  | .cellPop => { a with cellPop := arr }

def getArenaU8 (a : Algorithm.FlatHashLifeArena) : ArenaU8Field → Array UInt8
  | .l4HasRes => a.l4HasRes
  | .cellLevel => a.cellLevel

def setArenaU8 (a : Algorithm.FlatHashLifeArena) (f : ArenaU8Field) (arr : Array UInt8) :
    Algorithm.FlatHashLifeArena :=
  match f with
  | .l4HasRes => { a with l4HasRes := arr }
  | .cellLevel => { a with cellLevel := arr }

def updateArena (st : JvmState) (id : Nat) (f : Algorithm.FlatHashLifeArena → Algorithm.FlatHashLifeArena) :
    Option JvmState :=
  match st.heap.arenas[id]? with
  | some a => some { st with pc := st.pc + 1, heap := { st.heap with arenas := st.heap.arenas.set id (f a) } }
  | none => none

def stripMangle : String → String
  | "f_Algorithm_leafContains-fMEO4hA" => "f_Algorithm_leafContains"
  | "f_Algorithm_AsciiBytes_replicate___redArg-LMfZGw8" => "f_Algorithm_AsciiBytes_replicate___redArg"
  | "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" => "f_Algorithm_AsciiBytes_set___redArg"
  | "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" => "f_Algorithm_AsciiBytes_toStringRange"
  | "f_Algorithm_DagWriter_addLeaf-2TYgG_w" => "f_Algorithm_DagWriter_addLeaf"
  | "f_Algorithm_DagWriter_addNode-omp52vY" => "f_Algorithm_DagWriter_addNode"
  | "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY" => "f_Algorithm_FlatHashLifeArena_centeredHorizontal"
  | "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_centeredSubSubnode"
  | "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_centeredSubnode"
  | "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY" => "f_Algorithm_FlatHashLifeArena_centeredVertical"
  | "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE" => "f_Algorithm_FlatHashLifeArena_combineQuadrants"
  | "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY" => "f_Algorithm_FlatHashLifeArena_copyCellFromLoop"
  | "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc" => "f_Algorithm_FlatHashLifeArena_copyL4From"
  | "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY" => "f_Algorithm_FlatHashLifeArena_expandFrame"
  | "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY" => "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded"
  | "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY" => "f_Algorithm_FlatHashLifeArena_initRemapCellLoop"
  | "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY" => "f_Algorithm_FlatHashLifeArena_initRemapL4Loop"
  | "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantNE"
  | "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantNW"
  | "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantSE"
  | "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantSW"
  | "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY" => "f_Algorithm_FlatHashLifeArena_setCellStepRes"
  | "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE" => "f_Algorithm_FlatHashLifeArena_setL4StepRes"
  | "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY" => "f_Algorithm_FlatHashLifeArena_setRemapCell"
  | "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY" => "f_Algorithm_FlatHashLifeArena_setRemapL4"
  | "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ" => "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop"
  | "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_stepLevel4"
  | "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_stepLevel5"
  | "f_Algorithm_U64Buf_push-3yFGk1Y" => "f_Algorithm_U64Buf_push"
  | "f_Algorithm_cellBounds-iqUxbHk" => "f_Algorithm_cellBounds"
  | "f_Algorithm_cellBox-QwZRm1k" => "f_Algorithm_cellBox"
  | "f_Algorithm_cellNodeHash-bB1yPJE" => "f_Algorithm_cellNodeHash"
  | "f_Algorithm_cellToLeafBitUInt-feOb9K0" => "f_Algorithm_cellToLeafBitUInt"
  | "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk" => "f_Algorithm_centeredSubSubnodeSizeCell"
  | "f_Algorithm_computeLeafNextGen8x8BranchUInt-VKZWuLQ" => "f_Algorithm_computeLeafNextGen8x8BranchUInt"
  | "f_Algorithm_computeLeafNextGen8x8FastUInt-VKZWuLQ" => "f_Algorithm_computeLeafNextGen8x8FastUInt"
  | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0-2jIhpxI" =>
    "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0"
  | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0-VRmNplQ" =>
    "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0"
  | "f_Algorithm_computeNextGen4x4BitwiseUInt-WZ4Q5Ns" => "f_Algorithm_computeNextGen4x4BitwiseUInt"
  | "f_Algorithm_computePruneThresholds-fMEO4hA" => "f_Algorithm_computePruneThresholds"
  | "f_Algorithm_copyAscii-G2O0Dqo" => "f_Algorithm_copyAscii"
  | "f_Algorithm_copyCellTryStep-BzPDsQc" => "f_Algorithm_copyCellTryStep"
  | "f_Algorithm_copyU64-5j98i2w" => "f_Algorithm_copyU64"
  | "f_Algorithm_decimalLength-WZ4Q5Ns" => "f_Algorithm_decimalLength"
  | "f_Algorithm_decodeCharAt-BltQuoY" => "f_Algorithm_decodeCharAt"
  | "f_Algorithm_emptyAtHeight-WZ4Q5Ns" => "f_Algorithm_emptyAtHeight"
  | "f_Algorithm_emptyMacroCellUInt32_loop-t3GQkyU" => "f_Algorithm_emptyMacroCellUInt32_loop"
  | "f_Algorithm_fillGrid___redArg-RyWfpmY" => "f_Algorithm_fillGrid___redArg"
  | "f_Algorithm_findLastLeafX-8GdB7C8" => "f_Algorithm_findLastLeafX"
  | "f_Algorithm_formatCoordLine-feOb9K0" => "f_Algorithm_formatCoordLine"
  | "f_Algorithm_getCellStepRes-Qn1smSk" => "f_Algorithm_getCellStepRes"
  | "f_Algorithm_getRemapCell-Qn1smSk" => "f_Algorithm_getRemapCell"
  | "f_Algorithm_gridRows-G2O0Dqo" => "f_Algorithm_gridRows"
  | "f_Algorithm_leafRowMask-kBM7J_4" => "f_Algorithm_leafRowMask"
  | "f_Algorithm_level4Hash-2jIhpxI" => "f_Algorithm_level4Hash"
  | "f_Algorithm_makeLevel4Node-2jIhpxI" => "f_Algorithm_makeLevel4Node"
  | "f_Algorithm_serializeLife105_loop-KYAPeRw" => "f_Algorithm_serializeLife105_loop"
  | "f_Algorithm_serializeLife106_loop-B2nq9is" => "f_Algorithm_serializeLife106_loop"
  | "f_Algorithm_serializePlaintext-thtwfAY" => "f_Algorithm_serializePlaintext"
  | "f_Algorithm_serializeRLE-thtwfAY" => "f_Algorithm_serializeRLE"
  | "f_Algorithm_stepNGenerationsWith-OzbTU-A" => "f_Algorithm_stepNGenerationsWith"
  | "f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0-1A3ddvw" =>
    "f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0"
  | "f_Algorithm_DagWriter_addEntry-Z0ptBHY" => "f_Algorithm_DagWriter_addEntry"
  | "f_Algorithm_DagWriter_addLeafAt-7pzH9BY" => "f_Algorithm_DagWriter_addLeafAt"
  | "f_Algorithm_DagWriter_addNodeAt-jXDDuk8" => "f_Algorithm_DagWriter_addNodeAt"
  | "f_Algorithm_U64Buf_toArray-QwZRm1k" => "f_Algorithm_U64Buf_toArray"
  | "f_Algorithm_asciiStringLossy-BltQuoY" => "f_Algorithm_asciiStringLossy"
  | "f_Algorithm_cellBoundsLoop-Z0bPxiI" => "f_Algorithm_cellBoundsLoop"
  | "f_Algorithm_checkRLERule-BltQuoY" => "f_Algorithm_checkRLERule"
  | "f_Algorithm_copyPrefix___redArg-yOCu0fQ" => "f_Algorithm_copyPrefix___redArg"
  | "f_Algorithm_countChars-7IvYBaQ" => "f_Algorithm_countChars"
  | "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" => "f_Algorithm_decodeCharAt___lam__0"
  | "f_Algorithm_deserializeLife106_loop-65-6QV4" => "f_Algorithm_deserializeLife106_loop"
  | "f_Algorithm_deserializeMacrocell_loop-ocggIy4" => "f_Algorithm_deserializeMacrocell_loop"
  | "f_Algorithm_deserializePlaintext_loop-JllRuGI" => "f_Algorithm_deserializePlaintext_loop"
  | "f_Algorithm_emptyMacroCellUInt32-WZ4Q5Ns" => "f_Algorithm_emptyMacroCellUInt32"
  | "f_Algorithm_expandRuns-Wy9PQLY" => "f_Algorithm_expandRuns"
  | "f_Algorithm_findLastLeafRow-VKZWuLQ" => "f_Algorithm_findLastLeafRow"
  | "f_Algorithm_formatLeafNode-VKZWuLQ" => "f_Algorithm_formatLeafNode"
  | "f_Algorithm_formatLeafNode_loop-9LuH6mI" => "f_Algorithm_formatLeafNode_loop"
  | "f_Algorithm_formatLeafRow-8GdB7C8" => "f_Algorithm_formatLeafRow"
  | "f_Algorithm_formatLeafRow_loop-L5XE2Go" => "f_Algorithm_formatLeafRow_loop"
  | "f_Algorithm_formatMacrocellNode-bB1yPJE" => "f_Algorithm_formatMacrocellNode"
  | "f_Algorithm_formatRLEHeader-uqS13hg" => "f_Algorithm_formatRLEHeader"
  | "f_Algorithm_formatRLEItem-g_SBl1M" => "f_Algorithm_formatRLEItem"
  | "f_Algorithm_formatRLEItemLength-WZ4Q5Ns" => "f_Algorithm_formatRLEItemLength"
  | "f_Algorithm_gridItems-DRwJadE" => "f_Algorithm_gridItems"
  | "f_Algorithm_isRowRest-BltQuoY" => "f_Algorithm_isRowRest"
  | "f_Algorithm_keysToMacroCell-kVUmbH8" => "f_Algorithm_keysToMacroCell"
  | "f_Algorithm_leafFromKeys-tc6d2E8" => "f_Algorithm_leafFromKeys"
  | "f_Algorithm_leafWithCell-9LuH6mI" => "f_Algorithm_leafWithCell"
  | "f_Algorithm_levelForSpanLoop-8GdB7C8" => "f_Algorithm_levelForSpanLoop"
  | "f_Algorithm_life105Bounds-lLpu_l0" => "f_Algorithm_life105Bounds"
  | "f_Algorithm_life105Rest-dlT0rtU" => "f_Algorithm_life105Rest"
  | "f_Algorithm_macroCellAt-Qn1smSk" => "f_Algorithm_macroCellAt"
  | "f_Algorithm_macrocellCellChild-xsr7cmg" => "f_Algorithm_macrocellCellChild"
  | "f_Algorithm_macrocellLeafChild-jXDDuk8" => "f_Algorithm_macrocellLeafChild"
  | "f_Algorithm_macrocellSingleLeaf___lam__0-4PLdz1A" => "f_Algorithm_macrocellSingleLeaf___lam__0"
  | "f_Algorithm_macrocellSingleLeaf___lam__1-4PLdz1A" => "f_Algorithm_macrocellSingleLeaf___lam__1"
  | "f_Algorithm_macrocellSingleLeaf___lam__2-4PLdz1A" => "f_Algorithm_macrocellSingleLeaf___lam__2"
  | "f_Algorithm_parseBlocks-eSeeRns" => "f_Algorithm_parseBlocks"
  | "f_Algorithm_parseInt32At-BltQuoY" => "f_Algorithm_parseInt32At"
  | "f_Algorithm_parseRLEComments--R0mByA" => "f_Algorithm_parseRLEComments"
  | "f_Algorithm_parseRLEData-RjVw3pI" => "f_Algorithm_parseRLEData"
  | "f_Algorithm_parseRLEHeader___lam__0-XwsRtWc" => "f_Algorithm_parseRLEHeader___lam__0"
  | "f_Algorithm_parseRLEHeader___lam__1-BltQuoY" => "f_Algorithm_parseRLEHeader___lam__1"
  | "f_Algorithm_parseUInt32At-BltQuoY" => "f_Algorithm_parseUInt32At"
  | "f_Algorithm_relativeKeysLoop-CBMCY-A" => "f_Algorithm_relativeKeysLoop"
  | "f_Algorithm_scanDigitSet-7IvYBaQ" => "f_Algorithm_scanDigitSet"
  | "f_Algorithm_scanDigits-G4XTHLI" => "f_Algorithm_scanDigits"
  | "f_Algorithm_serializeLife105Block-WhflrNI" => "f_Algorithm_serializeLife105Block"
  | "f_Algorithm_skipDescriptions-BltQuoY" => "f_Algorithm_skipDescriptions"
  | "f_Algorithm_skipSpaces-BltQuoY" => "f_Algorithm_skipSpaces"
  | "f_Algorithm_splitKeys-0vDo7DQ" => "f_Algorithm_splitKeys"
  | "f_Algorithm_uint32ToInt32-WZ4Q5Ns" => "f_Algorithm_uint32ToInt32"
  | "f_Algorithm_wrapRLEItems-zax99WU" => "f_Algorithm_wrapRLEItems"
  | "f_Algorithm_writeDag-EGiNdXo" => "f_Algorithm_writeDag"
  | "f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg-4PLdz1A" =>
    "f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg"
  | s => s

def isSubtypeOf (objCls targetCls : String) : Bool :=
  objCls == targetCls || targetCls == "java/lang/Object" ||
    match targetCls, objCls with
    | "com/alexvanyo/composelife/model/Life105Status",
        "com/alexvanyo/composelife/model/Life105Status$InvalidHeader"
    | "com/alexvanyo/composelife/model/Life105Status",
        "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
    | "com/alexvanyo/composelife/model/Life105Status",
        "com/alexvanyo/composelife/model/Life105Status$Ok"
    | "com/alexvanyo/composelife/model/Life105Status",
        "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported"
    | "com/alexvanyo/composelife/model/Life105Warning",
        "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"
    | "com/alexvanyo/composelife/model/Life105Warning",
        "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput"
    | "com/alexvanyo/composelife/model/Life106Status",
        "com/alexvanyo/composelife/model/Life106Status$InvalidHeader"
    | "com/alexvanyo/composelife/model/Life106Status",
        "com/alexvanyo/composelife/model/Life106Status$InvalidLine"
    | "com/alexvanyo/composelife/model/Life106Status",
        "com/alexvanyo/composelife/model/Life106Status$EmptyFile"
    | "com/alexvanyo/composelife/model/Life106Status",
        "com/alexvanyo/composelife/model/Life106Status$Ok"
    | "com/alexvanyo/composelife/model/MacrocellStatus",
        "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
    | "com/alexvanyo/composelife/model/MacrocellStatus",
        "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput"
    | "com/alexvanyo/composelife/model/MacrocellStatus",
        "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId"
    | "com/alexvanyo/composelife/model/MacrocellStatus",
        "com/alexvanyo/composelife/model/MacrocellStatus$EmptyFile"
    | "com/alexvanyo/composelife/model/MacrocellStatus",
        "com/alexvanyo/composelife/model/MacrocellStatus$Ok"
    | "com/alexvanyo/composelife/model/MacrocellWarning",
        "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile"
    | "com/alexvanyo/composelife/model/MacrocellWarning",
        "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine"
    | "com/alexvanyo/composelife/model/MacrocellWarning",
        "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput"
    | "com/alexvanyo/composelife/model/PlaintextWarning",
        "com/alexvanyo/composelife/model/PlaintextWarning$EmptyFile"
    | "com/alexvanyo/composelife/model/PlaintextWarning",
        "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine"
    | "com/alexvanyo/composelife/model/PlaintextWarning",
        "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine"
    | "com/alexvanyo/composelife/model/PlaintextWarning",
        "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar"
    | "com/alexvanyo/composelife/model/RLEWarning",
        "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"
    | "com/alexvanyo/composelife/model/RLEWarning",
        "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset"
    | "com/alexvanyo/composelife/model/RLEWarning",
        "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar"
    | "com/alexvanyo/composelife/model/RLEWarning",
        "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput"
    | "com/alexvanyo/composelife/model/RLEWarning",
        "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" => true
    | _, _ => false

def checkInstanceOf : String → JvmVal → Bool :=
  let base := Jvm.defaultCheckInstanceOf fun cls ext =>
    match cls, ext with
    | "java/lang/Object", _ => true
    | "com/alexvanyo/composelife/model/HashLifeStepState", .hlState _ => true
    | "com/alexvanyo/composelife/model/MacroCell", .mc _ => true
    | "com/alexvanyo/composelife/model/MacroCell$CellNode", .mc (.cellNode ..) => true
    | "com/alexvanyo/composelife/model/MacroCell$Level4Node", .mc (.level4Node ..) => true
    | "com/alexvanyo/composelife/model/RLEStatus", .rleStatus _ => true
    | "kotlin/jvm/functions/Function1", .fnU64ToU32 _ => true
    | "kotlin/jvm/functions/Function1", .fnMcToU64 _ => true
    | "kotlin/jvm/functions/Function1", .fnMcToMc _ => true
    | "kotlin/jvm/functions/Function1", .fnMcToOptMc _ => true
    | "kotlin/jvm/functions/Function1", .fnHlToHl _ => true
    | _, _ => false
  fun cls v =>
    match v with
    | .allocRef objCls => isSubtypeOf objCls cls
    | _ => base cls v

def checkCast : String → JvmVal → Option JvmVal :=
  let base := Jvm.defaultCheckCast fun cls ext =>
    match cls, ext with
    | "java/lang/Object", _ => some (.ext ext)
    | "com/alexvanyo/composelife/model/HashLifeStepState", .hlState _ => some (.ext ext)
    | "com/alexvanyo/composelife/model/MacroCell", .mc _ => some (.ext ext)
    | "com/alexvanyo/composelife/model/MacroCell$CellNode", .mc (.cellNode ..) => some (.ext ext)
    | "com/alexvanyo/composelife/model/MacroCell$Level4Node", .mc (.level4Node ..) => some (.ext ext)
    | "com/alexvanyo/composelife/model/RLEStatus", .rleStatus _ => some (.ext ext)
    | "kotlin/jvm/functions/Function1", .fnU64ToU32 _ => some (.ext ext)
    | "kotlin/jvm/functions/Function1", .fnMcToU64 _ => some (.ext ext)
    | "kotlin/jvm/functions/Function1", .fnMcToMc _ => some (.ext ext)
    | "kotlin/jvm/functions/Function1", .fnMcToOptMc _ => some (.ext ext)
    | "kotlin/jvm/functions/Function1", .fnHlToHl _ => some (.ext ext)
    | _, _ => none
  fun cls v =>
    match v with
    | .allocRef objCls => if isSubtypeOf objCls cls then some v else none
    | _ => base cls v

def algResolveStatic (_st : JvmState) (cls field _desc : String) : Option JvmVal :=
  match cls, field with
  | "com/alexvanyo/composelife/model/Life105Status$Ok", "INSTANCE"
  | "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported", "INSTANCE"
  | "com/alexvanyo/composelife/model/Life105Warning$EmptyFile", "INSTANCE"
  | "com/alexvanyo/composelife/model/Life106Status$EmptyFile", "INSTANCE"
  | "com/alexvanyo/composelife/model/Life106Status$Ok", "INSTANCE"
  | "com/alexvanyo/composelife/model/MacrocellStatus$EmptyFile", "INSTANCE"
  | "com/alexvanyo/composelife/model/MacrocellStatus$Ok", "INSTANCE"
  | "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile", "INSTANCE"
  | "com/alexvanyo/composelife/model/RLEWarning$EmptyFile", "INSTANCE" =>
    some (.allocRef cls)
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "Companion" =>
    some (.allocRef "com/alexvanyo/composelife/model/MacroCell$Level4Node$Companion")
  | "com/alexvanyo/composelife/model/RLEStatus$EmptyFile", "INSTANCE" =>
    some (.ext (.rleStatus .emptyFile))
  | "com/alexvanyo/composelife/model/RLEStatus$Ok", "INSTANCE" =>
    some (.ext (.rleStatus .ok))
  | "com/alexvanyo/composelife/model/RLEStatus$RuleNotSupported", "INSTANCE" =>
    some (.ext (.rleStatus .ruleNotSupported))
  | _, _ => none

def boxCellBox (b : Int32 × Int32 × Int32 × Int32) : JvmVal :=
  .pair (.boxedInt b.1.toUInt32)
    (.pair (.boxedInt b.2.1.toUInt32)
      (.pair (.boxedInt b.2.2.1.toUInt32) (.boxedInt b.2.2.2.toUInt32)))

def algStepInvokeVirtual (st : JvmState) (cls method _desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, st.stack with
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "canCopySubgraphFrom",
      .ext (.arenaRef srcId) :: .ext (.arenaRef dstId) :: rest =>
    match st.heap.arenas[dstId]?, st.heap.arenas[srcId]? with
    | some dst, some src =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if dst.canCopySubgraphFrom src then 1 else 0) :: rest })
    | _, _ => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellCount-pVg5ArA", .ext (.arenaRef id) :: rest =>
    match st.heap.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.cellCount :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellMask-pVg5ArA", .ext (.arenaRef id) :: rest =>
    match st.heap.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.cellMask :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Count-pVg5ArA", .ext (.arenaRef id) :: rest =>
    match st.heap.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.l4Count :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getOverflow-w2LRezQ", .ext (.arenaRef id) :: rest =>
    match st.heap.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.overflow.toInt8.toInt32.toUInt32 :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "setOverflow-7apg3OU",
      v :: .ext (.arenaRef id) :: rest =>
    .inl (updateArena { st with stack := rest } id (fun a => { a with overflow := v.asI32.toUInt8 }))
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellLevel-TcUX1vc", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU8Ref id .cellLevel) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4HasRes-TcUX1vc", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU8Ref id .l4HasRes) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNe--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .cellNe) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNext--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .cellNext) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNw--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .cellNw) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSe--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .cellSe) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellStepRes--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .cellStepRes) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSw--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .cellSw) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Next--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .l4Next) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapCell--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .remapCell) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapL4--hP7Qyg", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU32Ref id .remapL4) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellPop-Y2RjT0g", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU64Ref id .cellPop) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Nw-Y2RjT0g", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU64Ref id .l4Nw) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Ne-Y2RjT0g", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU64Ref id .l4Ne) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Sw-Y2RjT0g", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU64Ref id .l4Sw) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Se-Y2RjT0g", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU64Ref id .l4Se) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4StepRes-Y2RjT0g", .ext (.arenaRef id) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.arenaU64Ref id .l4StepRes) :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internCellNode-gt5aIGQ",
      se :: sw :: ne :: nw :: lvl :: .ext (.arenaRef id) :: rest =>
    match st.heap.arenas[id]? with
    | some a =>
      let (resId, a') := a.internCellNode lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32
      .inl (some { st with
        pc := st.pc + 1, stack := .i32 resId :: rest,
        heap := { st.heap with arenas := st.heap.arenas.set id a' } })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internLevel4-PT-fW9Q",
      se :: sw :: ne :: nw :: .ext (.arenaRef id) :: rest =>
    match st.heap.arenas[id]? with
    | some a =>
      let (resId, a') := a.internLevel4 nw.asI64 ne.asI64 sw.asI64 se.asI64
      .inl (some { st with
        pc := st.pc + 1, stack := .i32 resId :: rest,
        heap := { st.heap with arenas := st.heap.arenas.set id a' } })
    | none => .inr none
  | "com/alexvanyo/composelife/model/HashLifeStepState", "getMacroCell", .ext (.hlState s) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.mc s.macroCell) :: rest })
  | "com/alexvanyo/composelife/model/HashLifeStepState", "getOffsetX", .ext (.hlState s) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 s.offsetX.toUInt32 :: rest })
  | "com/alexvanyo/composelife/model/HashLifeStepState", "getOffsetY", .ext (.hlState s) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 s.offsetY.toUInt32 :: rest })
  | "com/alexvanyo/composelife/model/StepPreparation", "getMacroCell", .ext (.stepPrep p) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.mc p.macroCell) :: rest })
  | "com/alexvanyo/composelife/model/StepPreparation", "getOffsetDelta", .ext (.stepPrep p) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 p.offsetDelta.toUInt32 :: rest })
  | "com/alexvanyo/composelife/model/MacroCell", "cellHashCode-pVg5ArA", .ext (.mc m) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 m.cellHashCode :: rest })
  | "com/alexvanyo/composelife/model/MacroCell", "level-pVg5ArA", .ext (.mc m) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 m.level :: rest })
  | "com/alexvanyo/composelife/model/MacroCell", "size-s-VKNKU", .ext (.mc m) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 m.size :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getHash-pVg5ArA",
      .ext (.mc (.cellNode h _ _ _ _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 h :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getNw", .ext (.mc (.cellNode _ nw _ _ _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.mc nw) :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getNe", .ext (.mc (.cellNode _ _ ne _ _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.mc ne) :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getSw", .ext (.mc (.cellNode _ _ _ sw _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.mc sw) :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getSe", .ext (.mc (.cellNode _ _ _ _ se)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.mc se) :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getHash-pVg5ArA",
      .ext (.mc (.level4Node h _ _ _ _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 h :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getNw-s-VKNKU",
      .ext (.mc (.level4Node _ nw _ _ _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 nw :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getNe-s-VKNKU",
      .ext (.mc (.level4Node _ _ ne _ _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 ne :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getSw-s-VKNKU",
      .ext (.mc (.level4Node _ _ _ sw _)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 sw :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getSe-s-VKNKU",
      .ext (.mc (.level4Node _ _ _ _ se)) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 se :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node$Companion", "invoke-2jIhpxI",
      se :: sw :: ne :: nw :: .allocRef "com/alexvanyo/composelife/model/MacroCell$Level4Node$Companion" :: rest =>
    .inl (some { st with
      pc := st.pc + 1,
      stack := .ext (.mc (Algorithm.makeLevel4Node nw.asI64 ne.asI64 sw.asI64 se.asI64)) :: rest })
  | _, _, _ => .inr none

def algStepInvokeSpecial (st : JvmState) (cls method _desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, st.stack with
  | "com/alexvanyo/composelife/model/HashLifeStepState", "<init>",
      .ext (.mc m) :: oy :: ox ::
      .allocRef "com/alexvanyo/composelife/model/HashLifeStepState" ::
      .allocRef "com/alexvanyo/composelife/model/HashLifeStepState" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.hlState ⟨ox.asI32.toInt32, oy.asI32.toInt32, m⟩) :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "<init>",
      .null :: .ext (.mc se) :: .ext (.mc sw) :: .ext (.mc ne) :: .ext (.mc nw) :: h ::
      .allocRef "com/alexvanyo/composelife/model/MacroCell$CellNode" ::
      .allocRef "com/alexvanyo/composelife/model/MacroCell$CellNode" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (.cellNode h.asI32 nw ne sw se)) :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "<init>",
      .null :: se :: sw :: ne :: nw :: h ::
      .allocRef "com/alexvanyo/composelife/model/MacroCell$Level4Node" ::
      .allocRef "com/alexvanyo/composelife/model/MacroCell$Level4Node" :: rest =>
    .inl (some { st with
      pc := st.pc + 1,
      stack := .ext (.mc (.level4Node h.asI32 nw.asI64 ne.asI64 sw.asI64 se.asI64)) :: rest })
  | "com/alexvanyo/composelife/model/PruneThresholds", "<init>",
      .null :: leaf :: mac ::
      .allocRef "com/alexvanyo/composelife/model/PruneThresholds" ::
      .allocRef "com/alexvanyo/composelife/model/PruneThresholds" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.pruneThresh ⟨mac.asI64, leaf.asI64⟩) :: rest })
  | "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader", "<init>",
      .str s ::
      .allocRef "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" ::
      .allocRef "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.rleStatus (.invalidHeader s)) :: rest })
  | "com/alexvanyo/composelife/model/StepBatchResult", "<init>",
      .ext (.pruneThresh pt) :: .ext (.hlState hs) ::
      .allocRef "com/alexvanyo/composelife/model/StepBatchResult" ::
      .allocRef "com/alexvanyo/composelife/model/StepBatchResult" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.stepBatch ⟨hs, pt⟩) :: rest })
  | "com/alexvanyo/composelife/model/StepPreparation", "<init>",
      .ext (.mc m) :: delta ::
      .allocRef "com/alexvanyo/composelife/model/StepPreparation" ::
      .allocRef "com/alexvanyo/composelife/model/StepPreparation" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.stepPrep ⟨delta.asI32.toInt32, m⟩) :: rest })
  | "com/alexvanyo/composelife/model/StepQuadrants", "<init>",
      .ext (.mc qse) :: .ext (.mc qsw) :: .ext (.mc qne) :: .ext (.mc qnw) ::
      .allocRef "com/alexvanyo/composelife/model/StepQuadrants" ::
      .allocRef "com/alexvanyo/composelife/model/StepQuadrants" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.stepQuad ⟨qnw, qne, qsw, qse⟩) :: rest })
  | "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput", "<init>",
      _marker :: col :: lineNum :: .str input ::
      .allocRef "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput" ::
      .allocRef "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput" :: rest =>
    .inl (some { st with
      pc := st.pc + 1, stack := .ext (.rleStatus (.unexpectedInput input lineNum.asI32 col.asI32)) :: rest })
  | "com/alexvanyo/composelife/algorithm/CellFrame$Node", "<init>",
      _marker :: k :: f2 :: f1 :: f0 ::
      .allocRef "com/alexvanyo/composelife/algorithm/CellFrame$Node" ::
      .allocRef "com/alexvanyo/composelife/algorithm/CellFrame$Node" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("f0", f0), ("f1", f1), ("f2", f2), ("f3", k)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/Life105Result", "<init>",
      _marker :: cells :: warns :: status ::
      .allocRef "com/alexvanyo/composelife/model/Life105Result" ::
      .allocRef "com/alexvanyo/composelife/model/Life105Result" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("status", status), ("warnings", warns), ("cells", cells)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/Life105Status$InvalidHeader", "<init>",
      line :: .allocRef "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" ::
      .allocRef "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("line", line)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput", "<init>",
      _marker :: col :: lineNum :: input ::
      .allocRef "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" ::
      .allocRef "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("input", input), ("lineIndex", lineNum), ("columnIndex", col)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput", "<init>",
      _marker :: col :: lineNum :: input ::
      .allocRef "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput" ::
      .allocRef "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("input", input), ("lineIndex", lineNum), ("columnIndex", col)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/Life106Result", "<init>",
      _marker :: cells :: status ::
      .allocRef "com/alexvanyo/composelife/model/Life106Result" ::
      .allocRef "com/alexvanyo/composelife/model/Life106Result" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("status", status), ("cells", cells)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/Life106Status$InvalidHeader", "<init>",
      line :: .allocRef "com/alexvanyo/composelife/model/Life106Status$InvalidHeader" ::
      .allocRef "com/alexvanyo/composelife/model/Life106Status$InvalidHeader" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("line", line)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/Life106Status$InvalidLine", "<init>",
      _marker :: line :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/Life106Status$InvalidLine" ::
      .allocRef "com/alexvanyo/composelife/model/Life106Status$InvalidLine" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum), ("line", line)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/MacrocellResult", "<init>",
      cell :: warns :: status ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellResult" ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellResult" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("status", status), ("warnings", warns), ("macroCell", cell)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader", "<init>",
      line :: .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader" ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("line", line)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput", "<init>",
      _marker :: lineNum :: input ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("input", input), ("lineIndex", lineNum)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId", "<init>",
      _marker :: n3 :: n2 :: n1 :: input ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId" ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId" :: rest =>
    let (addr, h') :=
      st.jvmHeap.alloc (.instance cls [("input", input), ("n1", n1), ("n2", n2), ("n3", n3)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine", "<init>",
      _marker :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine" ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput", "<init>",
      _marker :: input :: col :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput" ::
      .allocRef "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput" :: rest =>
    let (addr, h') :=
      st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum), ("columnIndex", col), ("input", input)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/PlaintextResult", "<init>",
      _marker :: cells :: warns ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextResult" ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextResult" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("warnings", warns), ("cells", cells)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine", "<init>",
      _marker :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine" ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine", "<init>",
      _marker :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine" ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar", "<init>",
      _marker :: ch :: col :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar" ::
      .allocRef "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar" :: rest =>
    let (addr, h') :=
      st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum), ("columnIndex", col), ("codePoint", ch)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/RLEResult", "<init>",
      _marker :: cells :: warns :: status ::
      .allocRef "com/alexvanyo/composelife/model/RLEResult" ::
      .allocRef "com/alexvanyo/composelife/model/RLEResult" :: rest =>
    let (addr, h') := st.jvmHeap.alloc (.instance cls [("status", status), ("warnings", warns), ("cells", cells)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd", "<init>",
      _marker :: cp :: col :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" :: rest =>
    let (addr, h') :=
      st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum), ("columnIndex", col), ("codePoint", cp)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset", "<init>",
      _marker :: y :: x :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" :: rest =>
    let (addr, h') :=
      st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum), ("x", x), ("y", y)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar", "<init>",
      _marker :: cp :: col :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" :: rest =>
    let (addr, h') :=
      st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum), ("columnIndex", col), ("codePoint", cp)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput", "<init>",
      _marker :: input :: col :: lineNum ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" ::
      .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" :: rest =>
    let (addr, h') :=
      st.jvmHeap.alloc (.instance cls [("lineIndex", lineNum), ("columnIndex", col), ("input", input)])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
  | _, _, _ => .inr none

def decodeBytes (st : JvmState) : JvmVal → Option ByteArray
  | .ext (.byteArr b) => some b
  | .heapRef addr =>
    match st.jvmHeap.get? addr with
    | some (.byteArray elems) => some ⟨elems⟩
    | _ => none
  | _ => none

def decodeStrArray (st : JvmState) : JvmVal → Option (Array String)
  | .strArr xs => some xs
  | .heapRef addr =>
    match st.jvmHeap.get? addr with
    | some (.objArray _ elems) =>
      elems.foldlM (fun acc v => match v with | .str s => some (acc.push s) | _ => none) #[]
    | _ => none
  | _ => none

def unboxI32 : JvmVal → UInt32
  | .i32 v | .boxedInt v | .boxedUInt v => v
  | v => v.asI32

def unboxI64 : JvmVal → UInt64
  | .i64 v | .boxedLong v | .boxedULong v => v
  | v => v.asI64

def unboxU8 : JvmVal → UInt8
  | .i32 v | .boxedByte v | .boxedUByte v | .boxedInt v | .boxedUInt v => v.toUInt8
  | v => v.asI32.toUInt8

def decodeU64List (h : Jvm.JvmHeap AlgExt) : Nat → JvmVal → Option (List UInt64)
  | 0, _ => none
  | fuel + 1, .heapRef addr =>
    match h.get? addr with
    | some (.objArray _ elems) =>
      match (elems[0]? : Option JvmVal) with
      | some (.boxedInt 0) => some []
      | some (.boxedInt 1) =>
        match (elems[1]? : Option JvmVal), (elems[2]? : Option JvmVal) with
        | some hd, some tl => (decodeU64List h fuel tl).map (unboxI64 hd :: ·)
        | _, _ => none
      | _ => none
    | _ => none
  | _, _ => none

def encodeU64List (h : Jvm.JvmHeap AlgExt) : List UInt64 → JvmVal × Jvm.JvmHeap AlgExt
  | [] =>
    let (addr, h') := h.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
    (.heapRef addr, h')
  | hd :: tl =>
    let (tlVal, h1) := encodeU64List h tl
    let (addr, h2) := h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedULong hd, tlVal])
    (.heapRef addr, h2)

def decodeLeafBucketList (h : Jvm.JvmHeap AlgExt) : Nat → JvmVal → Option (List (UInt64 × UInt32))
  | 0, _ => none
  | fuel + 1, .heapRef addr =>
    match h.get? addr with
    | some (.objArray _ elems) =>
      match (elems[0]? : Option JvmVal) with
      | some (.boxedInt 0) => some []
      | some (.boxedInt 1) =>
        match (elems[1]? : Option JvmVal), (elems[2]? : Option JvmVal) with
        | some (.pair k v), some tl =>
          (decodeLeafBucketList h fuel tl).map ((unboxI64 k, unboxI32 v) :: ·)
        | _, _ => none
      | _ => none
    | _ => none
  | _, _ => none

def encodeLeafBucketList (h : Jvm.JvmHeap AlgExt) :
    List (UInt64 × UInt32) → JvmVal × Jvm.JvmHeap AlgExt
  | [] =>
    let (addr, h') := h.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
    (.heapRef addr, h')
  | (k, v) :: tl =>
    let (tlVal, h1) := encodeLeafBucketList h tl
    let (addr, h2) :=
      h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .pair (.boxedULong k) (.boxedUInt v), tlVal])
    (.heapRef addr, h2)

private abbrev NodeKey := UInt32 × UInt32 × UInt32 × UInt32 × UInt32

def decodeNodeKey : JvmVal → Option NodeKey
  | .pair l (.pair nw (.pair ne (.pair sw se))) =>
    some (unboxI32 l, unboxI32 nw, unboxI32 ne, unboxI32 sw, unboxI32 se)
  | _ => none

def encodeNodeKey (k : NodeKey) : JvmVal :=
  .pair (.boxedUInt k.1)
    (.pair (.boxedUInt k.2.1)
      (.pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))))

def decodeNodeBucketList (h : Jvm.JvmHeap AlgExt) : Nat → JvmVal → Option (List (NodeKey × UInt32))
  | 0, _ => none
  | fuel + 1, .heapRef addr =>
    match h.get? addr with
    | some (.objArray _ elems) =>
      match (elems[0]? : Option JvmVal) with
      | some (.boxedInt 0) => some []
      | some (.boxedInt 1) =>
        match (elems[1]? : Option JvmVal), (elems[2]? : Option JvmVal) with
        | some (.pair kv v), some tl =>
          match decodeNodeKey kv, decodeNodeBucketList h fuel tl with
          | some k, some rest => some ((k, unboxI32 v) :: rest)
          | _, _ => none
        | _, _ => none
      | _ => none
    | _ => none
  | _, _ => none

def encodeNodeBucketList (h : Jvm.JvmHeap AlgExt) :
    List (NodeKey × UInt32) → JvmVal × Jvm.JvmHeap AlgExt
  | [] =>
    let (addr, h') := h.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
    (.heapRef addr, h')
  | (k, v) :: tl =>
    let (tlVal, h1) := encodeNodeBucketList h tl
    let (addr, h2) :=
      h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .pair (encodeNodeKey k) (.boxedUInt v), tlVal])
    (.heapRef addr, h2)

def decodeDagWriter (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.DagWriter
  | .ext (.dagWriter w) => some w
  | .heapRef addr =>
    match h.get? addr with
    | some (.objArray _ elems) =>
      match (elems[1]? : Option JvmVal), (elems[2]? : Option JvmVal), (elems[3]? : Option JvmVal) with
      | some (.ext (.strGrowBuf lines)), some (.heapRef lAddr), some (.heapRef nAddr) =>
        match h.get? lAddr, h.get? nAddr with
        | some (.objArray _ lBuckets), some (.objArray _ nBuckets) => do
          let fuel := h.objects.size + 2
          let leafT ← lBuckets.foldlM (fun acc v => (decodeLeafBucketList h fuel v).map acc.push) #[]
          let nodeT ← nBuckets.foldlM (fun acc v => (decodeNodeBucketList h fuel v).map acc.push) #[]
          return ⟨lines, leafT, nodeT⟩
        | _, _ => none
      | _, _, _ => none
    | _ => none
  | _ => none

def encodeDagWriter (h : Jvm.JvmHeap AlgExt) (w : Algorithm.DagWriter) : JvmVal × Jvm.JvmHeap AlgExt :=
  let (lBuckets, h1) : Array JvmVal × Jvm.JvmHeap AlgExt := w.leafT.foldl (fun (acc, curH) b =>
    let (bv, nextH) := encodeLeafBucketList curH b
    (acc.push bv, nextH)) (#[], h)
  let (nBuckets, h2) : Array JvmVal × Jvm.JvmHeap AlgExt := w.nodeT.foldl (fun (acc, curH) b =>
    let (bv, nextH) := encodeNodeBucketList curH b
    (acc.push bv, nextH)) (#[], h1)
  let (lAddr, h3) := h2.alloc (.objArray "java/lang/Object" lBuckets)
  let (nAddr, h4) := h3.alloc (.objArray "java/lang/Object" nBuckets)
  let (addr, h5) := h4.alloc (.objArray "java/lang/Object"
    #[.boxedInt 0, .ext (.strGrowBuf w.lines), .heapRef lAddr, .heapRef nAddr])
  (.heapRef addr, h5)

def copyObjArrayPrefix (srcElems dstElems : Array JvmVal) (n i : UInt32) : Nat → Array JvmVal
  | 0 => dstElems
  | fuel + 1 =>
    if i < n then
      let dst' := dstElems.set! i.toNat (srcElems[i.toNat]?.getD .null)
      copyObjArrayPrefix srcElems dst' n (i + 1) fuel
    else dstElems

def encodeOptScalarPair (h : Jvm.JvmHeap AlgExt) : Option (JvmVal × JvmVal) → JvmVal × Jvm.JvmHeap AlgExt
  | none =>
    let (addr, h') := h.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
    (.heapRef addr, h')
  | some (a, b) =>
    let (innerAddr, h1) := h.alloc (.objArray "java/lang/Object" #[.boxedInt 0, a, .null, .null, .null, b])
    let (outerAddr, h2) := h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr])
    (.heapRef outerAddr, h2)

def encodeGrowBufArray {α : Type} (h : Jvm.JvmHeap AlgExt) (f : Jvm.JvmHeap AlgExt → α → JvmVal × Jvm.JvmHeap AlgExt)
    (b : Algorithm.GrowBuf α) : JvmVal × Jvm.JvmHeap AlgExt :=
  let (vals, h1) : Array JvmVal × Jvm.JvmHeap AlgExt := b.toArray.foldl (fun (acc, ch) x =>
    let (v, nh) := f ch x
    (acc.push v, nh)) (#[], h)
  let (addr, h2) := h1.alloc (.objArray "java/lang/Object" vals)
  (.heapRef addr, h2)

def encodeLife105Warning (h : Jvm.JvmHeap AlgExt) : Algorithm.Life105Warning → JvmVal × Jvm.JvmHeap AlgExt
  | .emptyFile => (.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile", h)
  | .unexpectedInput inp ln col =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput"
      [("input", .str inp), ("lineIndex", .i32 ln), ("columnIndex", .i32 col)])
    (.heapRef a, h')

def decodeLife105Warning (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.Life105Warning
  | .allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile" => some .emptyFile
  | .heapRef addr =>
    match h.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput" flds) =>
      match flds.lookup "input", flds.lookup "lineIndex", flds.lookup "columnIndex" with
      | some (.str inp), some ln, some col => some (.unexpectedInput inp ln.asI32 col.asI32)
      | _, _, _ => none
    | _ => none
  | _ => none

def encodeLife105Result (h : Jvm.JvmHeap AlgExt) (u64s : List (Array UInt64))
    (res : Algorithm.Life105Result) : JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64) :=
  let (statusVal, h1) : JvmVal × Jvm.JvmHeap AlgExt := match res.status with
    | .ok => (.allocRef "com/alexvanyo/composelife/model/Life105Status$Ok", h)
    | .ruleNotSupported => (.allocRef "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported", h)
    | .invalidHeader line =>
      let (a, ha) := h.alloc (.instance "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" [("line", .str line)])
      (.heapRef a, ha)
    | .unexpectedInput inp ln col =>
      let (a, ha) := h.alloc (.instance "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
        [("input", .str inp), ("lineIndex", .i32 ln), ("columnIndex", .i32 col)])
      (.heapRef a, ha)
  let (warnVals, h2) : Array JvmVal × Jvm.JvmHeap AlgExt := res.warnings.foldl (fun (acc, ch) w =>
    let (wv, nh) := encodeLife105Warning ch w
    (acc.push wv, nh)) (#[], h1)
  let (wArrAddr, h3) := h2.alloc (.objArray "java/lang/Object" warnVals)
  let cId := u64s.length
  let u64s' := u64s ++ [res.cells]
  let (resAddr, h4) := h3.alloc (.instance "com/alexvanyo/composelife/model/Life105Result"
    [("status", statusVal), ("warnings", .heapRef wArrAddr), ("cells", .ext (.u64Ref cId))])
  (.heapRef resAddr, h4, u64s')

def encodeLife106Result (h : Jvm.JvmHeap AlgExt) (u64s : List (Array UInt64))
    (res : Algorithm.Life106Result) : JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64) :=
  let (statusVal, h1) : JvmVal × Jvm.JvmHeap AlgExt := match res.status with
    | .ok => (.allocRef "com/alexvanyo/composelife/model/Life106Status$Ok", h)
    | .emptyFile => (.allocRef "com/alexvanyo/composelife/model/Life106Status$EmptyFile", h)
    | .invalidHeader line =>
      let (a, ha) := h.alloc (.instance "com/alexvanyo/composelife/model/Life106Status$InvalidHeader" [("line", .str line)])
      (.heapRef a, ha)
    | .invalidLine ln line =>
      let (a, ha) := h.alloc (.instance "com/alexvanyo/composelife/model/Life106Status$InvalidLine"
        [("lineIndex", .i32 ln), ("line", .str line)])
      (.heapRef a, ha)
  let cId := u64s.length
  let u64s' := u64s ++ [res.cells]
  let (resAddr, h2) := h1.alloc (.instance "com/alexvanyo/composelife/model/Life106Result"
    [("status", statusVal), ("cells", .ext (.u64Ref cId))])
  (.heapRef resAddr, h2, u64s')

def decodeMacrocellWarning (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.MacrocellWarning
  | .allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile" => some .emptyFile
  | .heapRef addr =>
    match h.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine" flds) =>
      (flds.lookup "lineIndex").map fun v => .blankLine v.asI32
    | some (.instance "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput" flds) =>
      match flds.lookup "lineIndex", flds.lookup "columnIndex", flds.lookup "input" with
      | some ln, some col, some (.str inp) => some (.unexpectedInput ln.asI32 col.asI32 inp)
      | _, _, _ => none
    | _ => none
  | _ => none

def encodeMacrocellWarning (h : Jvm.JvmHeap AlgExt) : Algorithm.MacrocellWarning → JvmVal × Jvm.JvmHeap AlgExt
  | .emptyFile => (.allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile", h)
  | .blankLine ln =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine" [("lineIndex", .i32 ln)])
    (.heapRef a, h')
  | .unexpectedInput ln col inp =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput"
      [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("input", .str inp)])
    (.heapRef a, h')

def encodeMacrocellResult (h : Jvm.JvmHeap AlgExt) (res : Algorithm.MacrocellResult) :
    JvmVal × Jvm.JvmHeap AlgExt :=
  let (statusVal, h1) : JvmVal × Jvm.JvmHeap AlgExt := match res.status with
    | .ok => (.allocRef "com/alexvanyo/composelife/model/MacrocellStatus$Ok", h)
    | .emptyFile => (.allocRef "com/alexvanyo/composelife/model/MacrocellStatus$EmptyFile", h)
    | .invalidHeader line =>
      let (a, ha) := h.alloc (.instance "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader" [("line", .str line)])
      (.heapRef a, ha)
    | .unexpectedInput inp ln =>
      let (a, ha) := h.alloc (.instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput"
        [("input", .str inp), ("lineIndex", .i32 ln)])
      (.heapRef a, ha)
    | .unexpectedNodeId inp n1 n2 n3 =>
      let (a, ha) := h.alloc (.instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId"
        [("input", .str inp), ("n1", .i32 n1), ("n2", .i32 n2), ("n3", .i32 n3)])
      (.heapRef a, ha)
  let (warnVals, h2) : Array JvmVal × Jvm.JvmHeap AlgExt := res.warnings.foldl (fun (acc, ch) w =>
    let (wv, nh) := encodeMacrocellWarning ch w
    (acc.push wv, nh)) (#[], h1)
  let (wArrAddr, h3) := h2.alloc (.objArray "java/lang/Object" warnVals)
  let (resAddr, h4) := h3.alloc (.instance "com/alexvanyo/composelife/model/MacrocellResult"
    [("status", statusVal), ("warnings", .heapRef wArrAddr), ("macroCell", .ext (.mc res.macroCell))])
  (.heapRef resAddr, h4)

def decodePlaintextWarning (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.PlaintextWarning
  | .heapRef addr =>
    match h.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine" flds) =>
      (flds.lookup "lineIndex").map fun v => .blankLine v.asI32
    | some (.instance "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine" flds) =>
      (flds.lookup "lineIndex").map fun v => .shortLine v.asI32
    | some (.instance "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar" flds) =>
      match flds.lookup "lineIndex", flds.lookup "columnIndex", flds.lookup "codePoint" with
      | some ln, some col, some cp => some (.unexpectedChar ln.asI32 col.asI32 cp.asI32)
      | _, _, _ => none
    | _ => none
  | _ => none

def encodePlaintextWarning (h : Jvm.JvmHeap AlgExt) : Algorithm.PlaintextWarning → JvmVal × Jvm.JvmHeap AlgExt
  | .blankLine ln =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine" [("lineIndex", .i32 ln)])
    (.heapRef a, h')
  | .shortLine ln =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine" [("lineIndex", .i32 ln)])
    (.heapRef a, h')
  | .unexpectedChar ln col cp =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar"
      [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("codePoint", .i32 cp)])
    (.heapRef a, h')

def encodePlaintextResult (h : Jvm.JvmHeap AlgExt) (u64s : List (Array UInt64))
    (res : Algorithm.PlaintextResult) : JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64) :=
  let (warnVals, h1) : Array JvmVal × Jvm.JvmHeap AlgExt := res.warnings.foldl (fun (acc, ch) w =>
    let (wv, nh) := encodePlaintextWarning ch w
    (acc.push wv, nh)) (#[], h)
  let (wArrAddr, h2) := h1.alloc (.objArray "java/lang/Object" warnVals)
  let cId := u64s.length
  let u64s' := u64s ++ [res.cells]
  let (resAddr, h3) := h2.alloc (.instance "com/alexvanyo/composelife/model/PlaintextResult"
    [("warnings", .heapRef wArrAddr), ("cells", .ext (.u64Ref cId))])
  (.heapRef resAddr, h3, u64s')

def decodeRLEWarning (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.RLEWarning
  | .allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile" => some .emptyFile
  | .heapRef addr =>
    match h.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" flds) =>
      match flds.lookup "lineIndex", flds.lookup "x", flds.lookup "y" with
      | some ln, some x, some y => some (.duplicateOffset ln.asI32 x.asI32.toInt32 y.asI32.toInt32)
      | _, _, _ => none
    | some (.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" flds) =>
      match flds.lookup "lineIndex", flds.lookup "columnIndex", flds.lookup "codePoint" with
      | some ln, some col, some cp => some (.unexpectedChar ln.asI32 col.asI32 cp.asI32)
      | _, _, _ => none
    | some (.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" flds) =>
      match flds.lookup "lineIndex", flds.lookup "columnIndex", flds.lookup "input" with
      | some ln, some col, some (.str inp) => some (.unexpectedInput ln.asI32 col.asI32 inp)
      | _, _, _ => none
    | some (.instance "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" flds) =>
      match flds.lookup "lineIndex", flds.lookup "columnIndex", flds.lookup "codePoint" with
      | some ln, some col, some cp => some (.charAfterEnd ln.asI32 col.asI32 cp.asI32)
      | _, _, _ => none
    | _ => none
  | _ => none

def encodeRLEWarning (h : Jvm.JvmHeap AlgExt) : Algorithm.RLEWarning → JvmVal × Jvm.JvmHeap AlgExt
  | .emptyFile => (.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile", h)
  | .duplicateOffset ln x y =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset"
      [("lineIndex", .i32 ln), ("x", .i32 x.toUInt32), ("y", .i32 y.toUInt32)])
    (.heapRef a, h')
  | .unexpectedChar ln col cp =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar"
      [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("codePoint", .i32 cp)])
    (.heapRef a, h')
  | .unexpectedInput ln col inp =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput"
      [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("input", .str inp)])
    (.heapRef a, h')
  | .charAfterEnd ln col cp =>
    let (a, h') := h.alloc (.instance "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd"
      [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("codePoint", .i32 cp)])
    (.heapRef a, h')

def encodeRLEResult (h : Jvm.JvmHeap AlgExt) (u64s : List (Array UInt64))
    (res : Algorithm.RLEResult) : JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64) :=
  let (warnVals, h1) : Array JvmVal × Jvm.JvmHeap AlgExt := res.warnings.foldl (fun (acc, ch) w =>
    let (wv, nh) := encodeRLEWarning ch w
    (acc.push wv, nh)) (#[], h)
  let (wArrAddr, h2) := h1.alloc (.objArray "java/lang/Object" warnVals)
  let cId := u64s.length
  let u64s' := u64s ++ [res.cells]
  let (resAddr, h3) := h2.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
    [("status", .ext (.rleStatus res.status)), ("warnings", .heapRef wArrAddr), ("cells", .ext (.u64Ref cId))])
  (.heapRef resAddr, h3, u64s')

def algStepInvokeStatic (st : JvmState) (cls method desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, desc, st.stack with
  | "kotlin/ULongArray", "constructor-impl", "([J)[J", _ =>
    .inl (some { st with pc := st.pc + 1 })
  | "kotlin/UIntArray", "get-pVg5ArA", "([II)I", idx :: .ext (.arenaU32Ref id f) :: rest =>
    match st.heap.arenas[id]? with
    | some a =>
      let val := (getArenaU32 a f)[idx.asI32.toNat]!
      .inl (some { st with pc := st.pc + 1, stack := .i32 val :: rest })
    | none => .inr none
  | "kotlin/UIntArray", "getSize-impl", "([I)I", .ext (.arenaU32Ref id f) :: rest =>
    match st.heap.arenas[id]? with
    | some a =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (getArenaU32 a f).size.toUInt32 :: rest })
    | none => .inr none
  | "kotlin/UIntArray", "set-VXSXFK8", "([III)V", val :: idx :: .ext (.arenaU32Ref id f) :: rest =>
    .inl (updateArena { st with stack := rest } id
      (fun a => setArenaU32 a f ((getArenaU32 a f).set! idx.asI32.toNat val.asI32)))
  | "kotlin/UByteArray", "get-w2LRezQ", "([BI)B", idx :: .ext (.arenaU8Ref id f) :: rest =>
    match st.heap.arenas[id]? with
    | some a =>
      let val := (getArenaU8 a f)[idx.asI32.toNat]!
      .inl (some { st with pc := st.pc + 1, stack := .i32 val.toInt8.toInt32.toUInt32 :: rest })
    | none => .inr none
  | "kotlin/UByteArray", "set-VurrAj0", "([BIB)V", val :: idx :: .ext (.arenaU8Ref id f) :: rest =>
    .inl (updateArena { st with stack := rest } id
      (fun a => setArenaU8 a f ((getArenaU8 a f).set! idx.asI32.toNat val.asI32.toUInt8)))
  | "kotlin/ULongArray", "constructor-impl", "(I)[J", sz :: rest =>
    let newId := st.heap.u64Arrays.length
    let arr := Array.replicate sz.asI32.toNat 0
    .inl (some { st with
      pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
      heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [arr] } })
  | "kotlin/ULongArray", "get-s-VKNKU", "([JI)J", idx :: .ext (.arenaU64Ref id f) :: rest =>
    match st.heap.arenas[id]? with
    | some a =>
      let val := (getArenaU64 a f)[idx.asI32.toNat]!
      .inl (some { st with pc := st.pc + 1, stack := .i64 val :: rest })
    | none => .inr none
  | "kotlin/ULongArray", "get-s-VKNKU", "([JI)J", idx :: .ext (.u64Ref id) :: rest =>
    match st.heap.u64Arrays[id]? with
    | some arr =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (arr[idx.asI32.toNat]!) :: rest })
    | none => .inr none
  | "kotlin/ULongArray", "getSize-impl", "([J)I", .ext (.u64Ref id) :: rest =>
    match st.heap.u64Arrays[id]? with
    | some arr =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 arr.size.toUInt32 :: rest })
    | none => .inr none
  | "kotlin/ULongArray", "set-k8EXiF4", "([JIJ)V", val :: idx :: .ext (.u64Ref id) :: rest =>
    match st.heap.u64Arrays[id]? with
    | some arr =>
      .inl (some { st with
        pc := st.pc + 1, stack := rest,
        heap := { st.heap with u64Arrays := st.heap.u64Arrays.set id (arr.set! idx.asI32.toNat val.asI64) } })
    | none => .inr none
  | "kotlin/ULongArray", "set-k8EXiF4", "([JIJ)V", val :: idx :: .ext (.arenaU64Ref id f) :: rest =>
    .inl (updateArena { st with stack := rest } id
      (fun a => setArenaU64 a f ((getArenaU64 a f).set! idx.asI32.toNat val.asI64)))
  | "kotlin/collections/ArraysKt", "copyOfRange", "([JII)[J", e :: s :: .ext (.u64Ref id) :: rest =>
    match st.heap.u64Arrays[id]? with
    | some arr =>
      if s.asI32 < 0x80000000 && e.asI32 < 0x80000000 && s.asI32 <= e.asI32 && e.asI32.toNat <= arr.size then
        let newId := st.heap.u64Arrays.length
        let sub := arr.extract s.asI32.toNat e.asI32.toNat
        .inl (some { st with
          pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
          heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [sub] } })
      else .inr none
    | none => .inr none
  | _, _, _, _ =>
    let baseMethod := stripMangle method
    match baseMethod, st.stack with
    | "f_Algorithm_computeNextGen4x4BitwiseUInt", w :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.computeNextGen4x4BitwiseUInt w.asI32) :: rest })
    | "f_Algorithm_computeLeafNextGen8x8FastUInt", w :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.computeLeafNextGen8x8FastUInt w.asI64) :: rest })
    | "f_Algorithm_computeLeafNextGen8x8BranchUInt", w :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.computeLeafNextGen8x8BranchUInt w.asI64) :: rest })
    | "f_Algorithm_cellToLeafBitUInt", y :: x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.cellToLeafBitUInt x.asI32 y.asI32) :: rest })
    | "f_Algorithm_leafContains", y :: x :: leaf :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .i32 (if Algorithm.leafContains leaf.asI64 x.asI32 y.asI32 then 1 else 0) :: rest })
    | "f_Algorithm_cellNodeHash", se :: sw :: ne :: nw :: lvl :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .i32 (Algorithm.cellNodeHash lvl.asI32 nw.asI32 ne.asI32 sw.asI32 se.asI32) :: rest })
    | "f_Algorithm_level4Hash", se :: sw :: ne :: nw :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .i32 (Algorithm.level4Hash nw.asI64 ne.asI64 sw.asI64 se.asI64) :: rest })
    | "f_Algorithm_makeLevel4Node", se :: sw :: ne :: nw :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .ext (.mc (Algorithm.makeLevel4Node nw.asI64 ne.asI64 sw.asI64 se.asI64)) :: rest })
    | "f_Algorithm_makeCellNode", .ext (.mc se) :: .ext (.mc sw) :: .ext (.mc ne) :: .ext (.mc nw) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.makeCellNode nw ne sw se)) :: rest })
    | "f_Algorithm_MacroCell_cellEquals", .ext (.mc other) :: .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.MacroCell.cellEquals m other then 1 else 0) :: rest })
    | "f_Algorithm_centeredSubnode", .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.centeredSubnode m)) :: rest })
    | "f_Algorithm_centeredHorizontalSubnode", .ext (.mc e) :: .ext (.mc w) :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .ext (.mc (Algorithm.centeredHorizontalSubnode w e)) :: rest })
    | "f_Algorithm_centeredVerticalSubnode", .ext (.mc s) :: .ext (.mc n) :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .ext (.mc (Algorithm.centeredVerticalSubnode n s)) :: rest })
    | "f_Algorithm_centeredSubSubnodeFast", .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.centeredSubSubnodeFast m)) :: rest })
    | "f_Algorithm_centeredSubSubnodeSizeFast", .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (Algorithm.centeredSubSubnodeSizeFast m) :: rest })
    | "f_Algorithm_expandCentered", .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.expandCentered m)) :: rest })
    | "f_Algorithm_needToExpand", .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.needToExpand m then 1 else 0) :: rest })
    | "f_Algorithm_prepareStep", .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.stepPrep (Algorithm.prepareStep m)) :: rest })
    | "f_Algorithm_stepNGenerationsWith", .ext (.fnHlToHl fn) :: .ext (.hlState hs) :: step :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .ext (.hlState (Algorithm.stepNGenerationsWith step.asI32 hs fn)) :: rest })
    | "f_Algorithm_computePruneThresholds", leafKeep :: macKeep :: gens :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .ext (.pruneThresh (Algorithm.computePruneThresholds gens.asI64 macKeep.asI32 leafKeep.asI32)) :: rest })
    | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0",
        se :: sw :: ne :: nw :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .i64 (Algorithm.computeLevel4NextGen16x16UInt nw.asI64 ne.asI64 sw.asI64 se.asI64) :: rest })
    | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0",
        se :: sw :: ne :: nw :: .ext (.fnU64ToU32 fn) :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw.asI64 ne.asI64 sw.asI64 se.asI64 fn) :: rest })
    | "f_Algorithm_emptyAtHeight", h :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.emptyAtHeight h.asI32)) :: rest })
    | "f_Algorithm_cellsToMacroCell___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.emptyAtHeight 1)) :: rest })
    | "f_Algorithm_cellsToMacroCell___closed__1", rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .pair (.boxedULong 2147483648) (.ext (.mc (Algorithm.emptyAtHeight 1))) :: rest })
    | "f_Algorithm_importsAsEmpty", .ext (.mc m) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.importsAsEmpty m then 1 else 0) :: rest })
    | "f_Algorithm_leafRowMask", i :: b :: r :: t :: l :: y0 :: x0 :: leaf :: rest =>
      let res := Algorithm.leafRowMask leaf.asI64 x0.asI64.toInt64 y0.asI64.toInt64
        l.asI64.toInt64 t.asI64.toInt64 r.asI64.toInt64 b.asI64.toInt64 i.asI32
      .inl (some { st with pc := st.pc + 1, stack := .i64 res :: rest })
    | "f_List_isEmpty___redArg", .ext (.cellFrames fs) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if fs.isEmpty then 1 else 0) :: rest })
    | "f_List_isEmpty___redArg", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.objArray _ elems) =>
        let isEmpty := match (elems[0]? : Option JvmVal) with | some (.boxedInt 0) => true | _ => false
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if isEmpty then 1 else 0) :: rest })
      | _ => .inr none
    | "f_Algorithm_emptyMacroCellUInt32_loop", .ext (.mc curNode) :: curLevel :: level :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .ext (.mc (Algorithm.emptyMacroCellUInt32.loop level.asI32 curLevel.asI32 curNode)) :: rest })
    | "f_Algorithm_findLastLeafX___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 0 :: rest })
    | "f_Algorithm_findLastLeafX___closed__1", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 1 :: rest })
    | "f_Algorithm_findLastLeafX___closed__2", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 2 :: rest })
    | "f_Algorithm_findLastLeafX___closed__3", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 3 :: rest })
    | "f_Algorithm_findLastLeafX___closed__4", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 4 :: rest })
    | "f_Algorithm_findLastLeafX___closed__5", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 5 :: rest })
    | "f_Algorithm_findLastLeafX___closed__6", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 6 :: rest })
    | "f_Algorithm_findLastLeafX___closed__7", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 7 :: rest })
    | "f_Algorithm_findLastLeafX", y :: leaf :: rest =>
      let res := match Algorithm.findLastLeafX leaf.asI64 y.asI32 with
        | some v => .boxedUInt v
        | none => .null
      .inl (some { st with pc := st.pc + 1, stack := res :: rest })
    | "f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0", b :: a :: rest =>
      let optOf : JvmVal → Option UInt32
        | .null => none
        | .boxedUInt v => some v
        | .boxedInt v => some v
        | _ => none
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if optOf a == optOf b then 1 else 0) :: rest })
    | "f_Algorithm_DagWriter_addLeaf", leaf :: .ext (.dagWriter w) :: rest =>
      let r := w.addLeaf leaf.asI64
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.ext (.dagWriter r.2)) :: rest })
    | "f_Algorithm_DagWriter_addLeaf", leaf :: wVal :: rest =>
      match decodeDagWriter st.jvmHeap wVal with
      | some w =>
        let r := w.addLeaf leaf.asI64
        let (w', h') := encodeDagWriter st.jvmHeap r.2
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) w' :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_DagWriter_addNode", se :: sw :: ne :: nw :: lvl :: .ext (.dagWriter w) :: rest =>
      let r := w.addNode lvl.asI32 nw.asI32 ne.asI32 sw.asI32 se.asI32
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.ext (.dagWriter r.2)) :: rest })
    | "f_Algorithm_DagWriter_addNode", se :: sw :: ne :: nw :: lvl :: wVal :: rest =>
      match decodeDagWriter st.jvmHeap wVal with
      | some w =>
        let r := w.addNode lvl.asI32 nw.asI32 ne.asI32 sw.asI32 se.asI32
        let (w', h') := encodeDagWriter st.jvmHeap r.2
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) w' :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_centeredHorizontal", eId :: wId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredHorizontal wId.asI32 eId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_centeredVertical", sId :: nId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredVertical nId.asI32 sId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_centeredSubnode", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredSubnode nodeId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_centeredSubSubnode", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredSubSubnode nodeId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_centeredSubSubnodeSizeCell", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        .inl (some { st with
          pc := st.pc + 1, stack := .i64 (Algorithm.centeredSubSubnodeSizeCell a nodeId.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantNW", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantNW nodeId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantNE", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantNE nodeId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantSW", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantSW nodeId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantSE", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantSE nodeId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_combineQuadrants",
        se :: sw :: ne :: nw :: lvl :: nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.combineQuadrants nodeId.asI32 lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_stepLevel4", l4Id :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.stepLevel4 l4Id.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i64 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_stepLevel5", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        let (r, a') := a.stepLevel5 nodeId.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set id a' } })
      | none => .inr none
    | "f_Algorithm_getCellStepRes", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.getCellStepRes a nodeId.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_getRemapCell", nodeId :: .ext (.arenaRef id) :: rest =>
      match st.heap.arenas[id]? with
      | some a =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.getRemapCell a nodeId.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_setRemapL4", val :: idx :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setRemapL4 idx.asI32 val.asI32))
    | "f_Algorithm_FlatHashLifeArena_setRemapCell", val :: idx :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setRemapCell idx.asI32 val.asI32))
    | "f_Algorithm_FlatHashLifeArena_setCellStepRes", val :: idx :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setCellStepRes idx.asI32 val.asI32))
    | "f_Algorithm_FlatHashLifeArena_setL4StepRes", val :: idx :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setL4StepRes idx.asI32 val.asI64))
    | "f_Algorithm_FlatHashLifeArena_setOverflow", .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setOverflow))
    | "f_Algorithm_FlatHashLifeArena_expandFrame", base :: nodeId :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.expandFrame nodeId.asI32 base.asI32))
    | "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded", base :: nodeId :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.expandFrameIfNeeded nodeId.asI32 base.asI32))
    | "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop", fuel :: limit :: sp :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.stepCellSerialLoop sp.asI32 limit.asI32 fuel.asI32))
    | "f_Algorithm_FlatHashLifeArena_initRemapL4Loop", limit :: i :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.initRemapL4Loop i.asI32 limit.asI32))
    | "f_Algorithm_FlatHashLifeArena_initRemapCellLoop", limit :: i :: .ext (.arenaRef id) :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.initRemapCellLoop i.asI32 limit.asI32))
    | "f_Algorithm_FlatHashLifeArena_copyL4From",
        copyMemos :: l4Id :: .ext (.arenaRef srcId) :: .ext (.arenaRef dstId) :: rest =>
      match st.heap.arenas[dstId]?, st.heap.arenas[srcId]? with
      | some dst, some src =>
        let (r, dst') := dst.copyL4From src l4Id.asI32 (copyMemos.asI32 != 0)
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set dstId dst' } })
      | _, _ => .inr none
    | "f_Algorithm_copyCellTryStep",
        copyMemos :: cellId :: .ext (.arenaRef srcId) :: .ext (.arenaRef dstId) :: rest =>
      match st.heap.arenas[dstId]?, st.heap.arenas[srcId]? with
      | some dst, some src =>
        let (r, dst') := Algorithm.copyCellTryStep dst src cellId.asI32 (copyMemos.asI32 != 0)
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 r :: rest,
          heap := { st.heap with arenas := st.heap.arenas.set dstId dst' } })
      | _, _ => .inr none
    | "f_Algorithm_FlatHashLifeArena_copyCellFromLoop",
        fuel :: sp :: stackBase :: copyMemos :: .ext (.arenaRef srcId) :: .ext (.arenaRef dstId) :: rest =>
      match st.heap.arenas[dstId]?, st.heap.arenas[srcId]? with
      | some dst, some src =>
        let dst' := dst.copyCellFromLoop src (copyMemos.asI32 != 0) stackBase.asI32 sp.asI32 fuel.asI32
        .inl (some { st with
          pc := st.pc + 1, stack := rest,
          heap := { st.heap with arenas := st.heap.arenas.set dstId dst' } })
      | _, _ => .inr none
    | "f_Algorithm_GrowBuf_empty___redArg", .null :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", .str s :: .ext (.strGrowBuf b) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.strGrowBuf (b.push s)) :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", v :: .ext (.strGrowBuf b) :: rest =>
      if b.data.isEmpty && b.size == 0 then
        let ext? : Option AlgExt := match v with
          | .boxedULong u => some (.u64GrowBuf (Algorithm.GrowBuf.empty.push u))
          | .boxedBool f => some (.boolGrowBuf (Algorithm.GrowBuf.empty.push f))
          | .ext (.mc m) => some (.mcGrowBuf (Algorithm.GrowBuf.empty.push m))
          | .pair (.boxedUInt a) (.boxedUInt c) => some (.u32PairGrowBuf (Algorithm.GrowBuf.empty.push (a, c)))
          | .pair (.boxedUByte a) (.boxedUInt c) => some (.u8U32PairGrowBuf (Algorithm.GrowBuf.empty.push (a.toUInt8, c)))
          | _ =>
            match decodeRLEWarning st.jvmHeap v with
            | some w => some (.rleWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
            | none =>
              match decodeMacrocellWarning st.jvmHeap v with
              | some w => some (.mcWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
              | none => (decodePlaintextWarning st.jvmHeap v).map fun w =>
                  .ptWarnGrowBuf (Algorithm.GrowBuf.empty.push w)
        match ext? with
        | some e => .inl (some { st with pc := st.pc + 1, stack := .ext e :: rest })
        | none => .inr none
      else .inr none
    | "f_Algorithm_GrowBuf_push___redArg", .boxedULong u :: .ext (.u64GrowBuf b) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.u64GrowBuf (b.push u)) :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", .boxedBool f :: .ext (.boolGrowBuf b) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.boolGrowBuf (b.push f)) :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", .ext (.mc m) :: .ext (.mcGrowBuf b) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mcGrowBuf (b.push m)) :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", .pair (.boxedUInt a) (.boxedUInt c) :: .ext (.u32PairGrowBuf b) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.u32PairGrowBuf (b.push (a, c))) :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", .pair (.boxedUByte a) (.boxedUInt c) :: .ext (.u8U32PairGrowBuf b) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.u8U32PairGrowBuf (b.push (a.toUInt8, c))) :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", v :: .ext (.rleWarnGrowBuf b) :: rest =>
      match decodeRLEWarning st.jvmHeap v with
      | some w => .inl (some { st with pc := st.pc + 1, stack := .ext (.rleWarnGrowBuf (b.push w)) :: rest })
      | none => .inr none
    | "f_Algorithm_GrowBuf_push___redArg", v :: .ext (.mcWarnGrowBuf b) :: rest =>
      match decodeMacrocellWarning st.jvmHeap v with
      | some w => .inl (some { st with pc := st.pc + 1, stack := .ext (.mcWarnGrowBuf (b.push w)) :: rest })
      | none => .inr none
    | "f_Algorithm_GrowBuf_push___redArg", v :: .ext (.ptWarnGrowBuf b) :: rest =>
      match decodePlaintextWarning st.jvmHeap v with
      | some w => .inl (some { st with pc := st.pc + 1, stack := .ext (.ptWarnGrowBuf (b.push w)) :: rest })
      | none => .inr none
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.strGrowBuf b) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strArr b.toArray :: rest })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.u64GrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap (fun h x => (.boxedULong x, h)) b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.boolGrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap (fun h x => (.boxedBool x, h)) b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.mcGrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap (fun h x => (.ext (.mc x), h)) b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.u32PairGrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap (fun h x => (.pair (.boxedUInt x.1) (.boxedUInt x.2), h)) b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.u8U32PairGrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap (fun h x => (.pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2), h)) b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.rleWarnGrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap encodeRLEWarning b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.mcWarnGrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap encodeMacrocellWarning b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_GrowBuf_toArray___redArg", .ext (.ptWarnGrowBuf b) :: rest =>
      let (v, h') := encodeGrowBufArray st.jvmHeap encodePlaintextWarning b
      .inl (some { st with pc := st.pc + 1, stack := v :: rest, jvmHeap := h' })
    | "f_Algorithm_U64Buf_push", x :: .ext (.u64Ref id) :: rest =>
      match st.heap.u64Arrays[id]? with
      | some arr =>
        let pushed := Algorithm.U64Buf.push arr x.asI64
        let newId := st.heap.u64Arrays.length
        .inl (some { st with
          pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
          heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [pushed] } })
      | none => .inr none
    | "f_Algorithm_copyU64", .ext (.u64Ref dstId) :: i :: n :: .ext (.u64Ref srcId) :: rest =>
      match st.heap.u64Arrays[srcId]?, st.heap.u64Arrays[dstId]? with
      | some src, some dst =>
        let dst' := Algorithm.copyU64 src n.asI32 i.asI32 dst
        .inl (some { st with
          pc := st.pc + 1, stack := rest,
          heap := { st.heap with u64Arrays := st.heap.u64Arrays.set dstId dst' } })
      | _, _ => .inr none
    | "f_Algorithm_AsciiBytes_replicate___redArg", v :: n :: rest =>
      let b := v.asI32.toUInt8
      if hb : b < 128 then
        let newId := st.heap.asciiArrays.length
        let arr := Algorithm.AsciiBytes.replicate n.asI32 b hb
        .inl (some { st with
          pc := st.pc + 1, stack := .ext (.asciiRef newId) :: rest,
          heap := { st.heap with asciiArrays := st.heap.asciiArrays ++ [arr] } })
      else .inr none
    | "f_Algorithm_AsciiBytes_set___redArg", v :: i :: .ext (.asciiRef id) :: rest =>
      let b := v.asI32.toUInt8
      match st.heap.asciiArrays[id]? with
      | some g =>
        if hb : b < 128 then
          .inl (some { st with
            pc := st.pc + 1, stack := rest,
            heap := { st.heap with asciiArrays := st.heap.asciiArrays.set id (g.set i.asI32 b hb) } })
        else .inr none
      | none => .inr none
    | "f_Algorithm_AsciiBytes_set___redArg", v :: idx :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        let i := idx.asI32
        if !i.toBitVec.slt 0#32 then
          if h : i.toNat < elems.size then
            let h' := st.jvmHeap.set addr (.byteArray (elems.set i.toNat v.asI32.toUInt8 h))
            .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
          else .inl (some { st with pc := st.pc + 1, stack := rest })
        else .inl (some { st with pc := st.pc + 1, stack := rest })
      | _ => .inr none
    | "f_Algorithm_AsciiBytes_toStringRange", e :: s :: .ext (.asciiRef id) :: rest =>
      match st.heap.asciiArrays[id]? with
      | some g =>
        .inl (some { st with pc := st.pc + 1, stack := .str (g.toStringRange s.asI32 e.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_fillGrid___redArg",
        .ext (.asciiRef gId) :: limit :: i :: alive :: h :: w :: minY :: minX :: .ext (.u64Ref cId) :: rest =>
      let ab := alive.asI32.toUInt8
      match st.heap.u64Arrays[cId]?, st.heap.asciiArrays[gId]? with
      | some cells, some g =>
        if ha : ab < 128 then
          let g' := Algorithm.fillGrid cells minX.asI32.toInt32 minY.asI32.toInt32 w.asI32 h.asI32 ab ha i.asI32 limit.asI32 g
          .inl (some { st with
            pc := st.pc + 1, stack := rest,
            heap := { st.heap with asciiArrays := st.heap.asciiArrays.set gId g' } })
        else .inr none
      | _, _ => .inr none
    | "f_Algorithm_gridRows", .ext (.strGrowBuf acc) :: r :: h :: w :: .ext (.asciiRef gId) :: rest =>
      match st.heap.asciiArrays[gId]? with
      | some g =>
        .inl (some { st with
          pc := st.pc + 1,
          stack := .ext (.strGrowBuf (Algorithm.gridRows g w.asI32 h.asI32 r.asI32 acc)) :: rest })
      | none => .inr none
    | "f_Algorithm_copyAscii", .ext (.asciiRef gId) :: k :: n :: s :: .ext (.byteArr bytes) :: rest =>
      match st.heap.asciiArrays[gId]? with
      | some g =>
        let g' := Algorithm.copyAscii bytes s.asI32 n.asI32 k.asI32 g
        .inl (some { st with
          pc := st.pc + 1, stack := rest,
          heap := { st.heap with asciiArrays := st.heap.asciiArrays.set gId g' } })
      | none => .inr none
    | "f_Algorithm_formatBlockHeader", y :: x :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .str (Algorithm.formatBlockHeader x.asI32.toInt32 y.asI32.toInt32) :: rest })
    | "f_Algorithm_formatCoordLine", y :: x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str (Algorithm.formatCoordLine x.asI32 y.asI32) :: rest })
    | "f_Algorithm_serializeLife105___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strArr #[] :: rest })
    | "f_Algorithm_serializeLife105_loop",
        .ext (.strGrowBuf acc) :: j :: .strArr block :: .ext (.u64Ref cId) :: fuel :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with
          pc := st.pc + 1,
          stack := .ext (.strGrowBuf (Algorithm.serializeLife105.loop fuel.asI32 cells block j.asI32 acc)) :: rest })
      | none => .inr none
    | "f_Algorithm_serializeLife106_loop",
        .ext (.strGrowBuf acc) :: limit :: i :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with
          pc := st.pc + 1,
          stack := .ext (.strGrowBuf (Algorithm.serializeLife106.loop cells i.asI32 limit.asI32 acc)) :: rest })
      | none => .inr none
    | "f_Algorithm_cellBounds", maxY :: minY :: maxX :: minX :: limit :: i :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        let b := Algorithm.cellBounds cells i.asI32 limit.asI32
          minX.asI32.toInt32 maxX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32
        .inl (some { st with pc := st.pc + 1, stack := boxCellBox b :: rest })
      | none => .inr none
    | "f_Algorithm_cellBox", .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with pc := st.pc + 1, stack := boxCellBox (Algorithm.cellBox cells) :: rest })
      | none => .inr none
    | "f_Algorithm_decodeCharAt", limit :: p :: .ext (.byteArr bytes) :: rest =>
      let r := Algorithm.decodeCharAt bytes p.asI32 limit.asI32
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest })
    | "f_Algorithm_decodeCharAt", limit :: p :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        let r := Algorithm.decodeCharAt ⟨elems⟩ p.asI32 limit.asI32
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest })
      | _ => .inr none
    | "f_Algorithm_serializePlaintext___closed__1", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strArr #["."] :: rest })
    | "f_Algorithm_serializePlaintext", maxY :: minY :: maxX :: minX :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with
          pc := st.pc + 1,
          stack := .strArr (Algorithm.serializePlaintext cells
            minX.asI32.toInt32 maxX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32) :: rest })
      | none => .inr none
    | "f_Algorithm_decimalLength", n :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.decimalLength n.asI32) :: rest })
    | "f_Algorithm_serializeRLE", maxY :: minY :: maxX :: minX :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with
          pc := st.pc + 1,
          stack := .strArr (Algorithm.serializeRLE cells
            minX.asI32.toInt32 maxX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32) :: rest })
      | none => .inr none
    | "f_Algorithm_DagWriter_addEntry", c4 :: c3 :: c2 :: c1 :: .ext (.mc m) :: .ext (.dagWriter w) :: rest =>
      let r := w.addEntry m c1.asI32 c2.asI32 c3.asI32 c4.asI32
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.ext (.dagWriter r.2)) :: rest })
    | "f_Algorithm_DagWriter_addEntry", c4 :: c3 :: c2 :: c1 :: .ext (.mc m) :: wVal :: rest =>
      match decodeDagWriter st.jvmHeap wVal with
      | some w =>
        let r := w.addEntry m c1.asI32 c2.asI32 c3.asI32 c4.asI32
        let (w', h') := encodeDagWriter st.jvmHeap r.2
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) w' :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_DagWriter_addLeafAt", s :: leaf :: .ext (.dagWriter w) :: rest =>
      let r := w.addLeafAt leaf.asI64 s.asI32
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.ext (.dagWriter r.2)) :: rest })
    | "f_Algorithm_DagWriter_addLeafAt", s :: leaf :: wVal :: rest =>
      match decodeDagWriter st.jvmHeap wVal with
      | some w =>
        let r := w.addLeafAt leaf.asI64 s.asI32
        let (w', h') := encodeDagWriter st.jvmHeap r.2
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) w' :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_DagWriter_addNodeAt", s :: kVal :: .ext (.dagWriter w) :: rest =>
      match decodeNodeKey kVal with
      | some k =>
        let r := w.addNodeAt k s.asI32
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.ext (.dagWriter r.2)) :: rest })
      | none => .inr none
    | "f_Algorithm_DagWriter_addNodeAt", s :: kVal :: wVal :: rest =>
      match decodeNodeKey kVal, decodeDagWriter st.jvmHeap wVal with
      | some k, some w =>
        let r := w.addNodeAt k s.asI32
        let (w', h') := encodeDagWriter st.jvmHeap r.2
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) w' :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "f_Algorithm_U64Buf_empty", rest =>
      let newId := st.heap.u64Arrays.length
      .inl (some { st with
        pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
        heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [Algorithm.U64Buf.empty] } })
    | "f_Algorithm_U64Buf_toArray", .ext (.u64Ref id) :: rest =>
      match st.heap.u64Arrays[id]? with
      | some arr =>
        let newId := st.heap.u64Arrays.length
        .inl (some { st with
          pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
          heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [Algorithm.U64Buf.toArray arr] } })
      | none => .inr none
    | "f_Algorithm_asciiStringLossy", e :: s :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        .inl (some { st with pc := st.pc + 1, stack := .str (Algorithm.asciiStringLossy bytes s.asI32 e.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_cellBoundsLoop", maxY :: maxX :: minY :: minX :: limit :: i :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        let r := Algorithm.cellBoundsLoop cells i.asI32 limit.asI32 minX.asI64 minY.asI64 maxX.asI64 maxY.asI64
        let boxed := .pair (.boxedULong r.1) (.pair (.boxedULong r.2.1) (.pair (.boxedULong r.2.2.1) (.boxedULong r.2.2.2)))
        .inl (some { st with pc := st.pc + 1, stack := boxed :: rest })
      | none => .inr none
    | "f_Algorithm_cellsToMacroCell___closed__2", rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .pair (.boxedULong 2147483648) (.pair (.boxedULong 2147483648) (.ext (.mc (Algorithm.emptyAtHeight 1)))) :: rest })
    | "f_Algorithm_checkRLERule", limit :: pos :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.checkRLERule bytes pos.asI32 limit.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_checkRuleLine", bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.checkRuleLine bytes) :: rest })
      | none => .inr none
    | "f_Algorithm_copyPrefix___redArg",
        .heapRef dstAddr :: i :: n :: .heapRef srcAddr :: _inst :: rest =>
      match st.jvmHeap.get? srcAddr, st.jvmHeap.get? dstAddr with
      | some (.objArray _ srcElems), some (.objArray dstCls dstElems) =>
        let dst' := copyObjArrayPrefix srcElems dstElems n.asI32 i.asI32 (n.asI32.toNat + 1)
        .inl (some { st with
          pc := st.pc + 1, stack := rest,
          jvmHeap := st.jvmHeap.set dstAddr (.objArray dstCls dst') })
      | _, _ => .inr none
    | "f_Algorithm_countChars", n :: p :: limit :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.countChars bytes limit.asI32 p.asI32 n.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_decodeCharAt___lam__0", k :: .heapRef addr :: p :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        let idx := p.asI32 + k.asI32
        if idx.toBitVec.slt 0#32 then .inr none
        else if h : idx.toNat < elems.size then
          let b := elems[idx.toNat].toUInt32 &&& 0x3F
          .inl (some { st with pc := st.pc + 1, stack := .i32 b :: rest })
        else .inr none
      | _ => .inr none
    | "f_Algorithm_deserializeLife105___closed__1", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_deserializeLife105___closed__2", rest =>
      let (resVal, h', u64s') := encodeLife105Result st.jvmHeap st.heap.u64Arrays ⟨.ok, #[], #[]⟩
      .inl (some { st with
        pc := st.pc + 1, stack := resVal :: rest,
        jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
    | "f_Algorithm_deserializeLife105___closed__3", rest =>
      let (resVal, h', u64s') := encodeLife105Result st.jvmHeap st.heap.u64Arrays ⟨.ruleNotSupported, #[], #[]⟩
      .inl (some { st with
        pc := st.pc + 1, stack := resVal :: rest,
        jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
    | "f_Algorithm_deserializeLife105___closed__5", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object"
        #[.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_deserializeLife105___closed__6", rest =>
      let (resVal, h', u64s') := encodeLife105Result st.jvmHeap st.heap.u64Arrays ⟨.ok, #[.emptyFile], #[]⟩
      .inl (some { st with
        pc := st.pc + 1, stack := resVal :: rest,
        jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
    | "f_Algorithm_deserializeLife106___closed__1", rest =>
      let (resVal, h', u64s') := encodeLife106Result st.jvmHeap st.heap.u64Arrays ⟨.emptyFile, #[]⟩
      .inl (some { st with
        pc := st.pc + 1, stack := resVal :: rest,
        jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
    | "f_Algorithm_deserializeLife106_loop", .ext (.u64Ref accId) :: limit :: i :: linesVal :: rest =>
      match decodeStrArray st linesVal, st.heap.u64Arrays[accId]? with
      | some lines, some acc =>
        let res := Algorithm.deserializeLife106.loop lines i.asI32 limit.asI32 acc
        let (resVal, h', u64s') := encodeLife106Result st.jvmHeap st.heap.u64Arrays res
        .inl (some { st with
          pc := st.pc + 1, stack := resVal :: rest,
          jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
      | _, _ => .inr none
    | "f_Algorithm_deserializeMacrocell___closed__0", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_deserializeMacrocell___closed__1", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object"
        #[.allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile"])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_deserializeMacrocell___closed__2", rest =>
      let (resVal, h') := encodeMacrocellResult st.jvmHeap ⟨.emptyFile, #[.emptyFile], Algorithm.emptyLevel4⟩
      .inl (some { st with pc := st.pc + 1, stack := resVal :: rest, jvmHeap := h' })
    | "f_Algorithm_deserializeMacrocell_loop",
        warnsVal :: isLeafVal :: leavesVal :: nodesVal :: leaf :: y :: x :: col :: p ::
        limit :: bytesVal :: inLeaf :: i :: numLines :: linesVal :: rest =>
      let nodes? : Option (Algorithm.GrowBuf Algorithm.MacroCell) := match nodesVal with
        | .ext (.mcGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      let leaves? : Option (Algorithm.GrowBuf UInt64) := match leavesVal with
        | .ext (.u64GrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      let isLeaf? : Option (Algorithm.GrowBuf Bool) := match isLeafVal with
        | .ext (.boolGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      let warns? : Option (Algorithm.GrowBuf Algorithm.MacrocellWarning) := match warnsVal with
        | .ext (.mcWarnGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match decodeStrArray st linesVal, decodeBytes st bytesVal, nodes?, leaves?, isLeaf?, warns? with
      | some lines, some bytes, some nodes, some leaves, some isLeaf, some warns =>
        let res := Algorithm.deserializeMacrocell.loop lines numLines.asI32 i.asI32 (inLeaf.asI32 != 0)
          bytes limit.asI32 p.asI32 col.asI32 x.asI32 y.asI32 leaf.asI64 nodes leaves isLeaf warns
        let (resVal, h') := encodeMacrocellResult st.jvmHeap res
        .inl (some { st with pc := st.pc + 1, stack := resVal :: rest, jvmHeap := h' })
      | _, _, _, _, _, _ => .inr none
    | "f_Algorithm_deserializePlaintext_loop",
        .ext (.u64Ref cId) :: warnsVal :: hasLongest :: longestLen :: longestIdx :: rowIdx ::
        col :: p :: limit :: bytesVal :: inRow :: i :: numLines :: linesVal :: rest =>
      let warns? : Option (Algorithm.GrowBuf Algorithm.PlaintextWarning) := match warnsVal with
        | .ext (.ptWarnGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match decodeStrArray st linesVal, decodeBytes st bytesVal, warns?, st.heap.u64Arrays[cId]? with
      | some lines, some bytes, some warns, some cells =>
        let res := Algorithm.deserializePlaintext.loop lines numLines.asI32 i.asI32 (inRow.asI32 != 0)
          bytes limit.asI32 p.asI32 col.asI32 rowIdx.asI32 longestIdx.asI32 longestLen.asI32
          (hasLongest.asI32 != 0) warns cells
        let (resVal, h', u64s') := encodePlaintextResult st.jvmHeap st.heap.u64Arrays res
        .inl (some { st with
          pc := st.pc + 1, stack := resVal :: rest,
          jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
      | _, _, _, _ => .inr none
    | "f_Algorithm_deserializeRLE___closed__0", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object"
        #[.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_deserializeRLE___closed__1", rest =>
      let (resVal, h', u64s') := encodeRLEResult st.jvmHeap st.heap.u64Arrays ⟨.emptyFile, #[.emptyFile], #[]⟩
      .inl (some { st with
        pc := st.pc + 1, stack := resVal :: rest,
        jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
    | "f_Algorithm_emptyMacroCellUInt32", lvl :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.emptyMacroCellUInt32 lvl.asI32)) :: rest })
    | "f_Algorithm_expandRuns", .ext (.u64Ref cId) :: startX :: y :: x :: k :: j :: numRuns :: .heapRef runsAddr :: rest =>
      match st.jvmHeap.get? runsAddr, st.heap.u64Arrays[cId]? with
      | some (.objArray _ elems), some cells =>
        let runsOpt := elems.foldlM (fun acc v => match v with
          | .pair a b => some (acc.push (unboxI32 a, unboxI32 b))
          | _ => none) #[]
        match runsOpt with
        | some runs =>
          let res := Algorithm.expandRuns runs numRuns.asI32 j.asI32 k.asI32
            x.asI32.toInt32 y.asI32.toInt32 startX.asI32.toInt32 cells
          let newId := st.heap.u64Arrays.length
          .inl (some { st with
            pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
            heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [res] } })
        | none => .inr none
      | _, _ => .inr none
    | "f_Algorithm_expandRuns___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt 0) (.boxedUInt 0) :: rest })
    | "f_Algorithm_findLastLeafRow", leaf :: rest =>
      let res := match Algorithm.findLastLeafRow leaf.asI64 with
        | some v => .boxedUInt v
        | none => .null
      .inl (some { st with pc := st.pc + 1, stack := res :: rest })
    | "f_Algorithm_finishRLE", startY :: startX :: runsVal :: warnsVal :: rest =>
      let warns? : Option (Algorithm.GrowBuf Algorithm.RLEWarning) := match warnsVal with
        | .ext (.rleWarnGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      let runs? : Option (Algorithm.GrowBuf (UInt32 × UInt32)) := match runsVal with
        | .ext (.u32PairGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match warns?, runs? with
      | some warns, some runs =>
        let res := Algorithm.finishRLE warns runs startX.asI32.toInt32 startY.asI32.toInt32
        let (resVal, h', u64s') := encodeRLEResult st.jvmHeap st.heap.u64Arrays res
        .inl (some { st with
          pc := st.pc + 1, stack := resVal :: rest,
          jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
      | _, _ => .inr none
    | "f_Algorithm_formatLeafNode", leaf :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str (Algorithm.formatLeafNode leaf.asI64) :: rest })
    | "f_Algorithm_formatLeafNode_loop", .str acc :: limit :: y :: leaf :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .str (Algorithm.formatLeafNode.loop leaf.asI64 y.asI32 limit.asI32 acc) :: rest })
    | "f_Algorithm_formatLeafRow", y :: leaf :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str (Algorithm.formatLeafRow leaf.asI64 y.asI32) :: rest })
    | "f_Algorithm_formatLeafRow_loop", .str acc :: limit :: x :: y :: leaf :: rest =>
      .inl (some { st with
        pc := st.pc + 1, stack := .str (Algorithm.formatLeafRow.loop leaf.asI64 y.asI32 x.asI32 limit.asI32 acc) :: rest })
    | "f_Algorithm_formatMacrocellNode", se :: sw :: ne :: nw :: lvl :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .str (Algorithm.formatMacrocellNode lvl.asI32 nw.asI32 ne.asI32 sw.asI32 se.asI32) :: rest })
    | "f_Algorithm_formatRLEHeader", height :: width :: minY :: minX :: rest =>
      let arr := Algorithm.formatRLEHeader minX.asI32.toInt32 minY.asI32.toInt32 width.asI32 height.asI32
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" (arr.map .str))
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_formatRLEItem", count :: tag :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str (Algorithm.formatRLEItem tag.asI32.toUInt8 count.asI32) :: rest })
    | "f_Algorithm_formatRLEItemLength", count :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.formatRLEItemLength count.asI32) :: rest })
    | "f_Algorithm_gridItems",
        itemsVal :: rowEnds :: runLen :: runTag :: k :: total :: w :: .ext (.asciiRef gId) :: rest =>
      let items? : Option (Algorithm.GrowBuf (UInt8 × UInt32)) := match itemsVal with
        | .ext (.u8U32PairGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match st.heap.asciiArrays[gId]?, items? with
      | some g, some items =>
        let r := Algorithm.gridItems g w.asI32 total.asI32 k.asI32 runTag.asI32.toUInt8
          runLen.asI32 rowEnds.asI32 items
        .inl (some { st with pc := st.pc + 1, stack := .ext (.u8U32PairGrowBuf r) :: rest })
      | _, _ => .inr none
    | "f_Algorithm_isRowLine", bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.isRowLine bytes then 1 else 0) :: rest })
      | none => .inr none
    | "f_Algorithm_isRowRest", p :: limit :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        let r := Algorithm.isRowRest ⟨elems⟩ limit.asI32 p.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if r then 1 else 0) :: rest })
      | _ => .inr none
    | "f_Algorithm_keysToMacroCell", .ext (.mc empty) :: h :: y0 :: x0 :: keysVal :: rest =>
      match decodeU64List st.jvmHeap (st.jvmHeap.objects.size + 2) keysVal with
      | some keys =>
        .inl (some { st with
          pc := st.pc + 1,
          stack := .ext (.mc (Algorithm.keysToMacroCell keys x0.asI64 y0.asI64 h.asI32 empty)) :: rest })
      | none => .inr none
    | "f_Algorithm_leafFromKeys", leaf :: y0 :: x0 :: keysVal :: rest =>
      match decodeU64List st.jvmHeap (st.jvmHeap.objects.size + 2) keysVal with
      | some keys =>
        .inl (some { st with
          pc := st.pc + 1, stack := .i64 (Algorithm.leafFromKeys keys x0.asI64 y0.asI64 leaf.asI64) :: rest })
      | none => .inr none
    | "f_Algorithm_leafWithCell", isAlive :: y :: x :: leaf :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .i64 (Algorithm.leafWithCell leaf.asI64 x.asI32 y.asI32 (isAlive.asI32 != 0)) :: rest })
    | "f_Algorithm_levelForSpanLoop", lvl :: span :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.levelForSpanLoop span.asI64 lvl.asI32) :: rest })
    | "f_Algorithm_life105Bounds", maxY :: minY :: minX :: limit :: i :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        let r := Algorithm.life105Bounds cells i.asI32 limit.asI32
          minX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32
        .inl (some { st with
          pc := st.pc + 1,
          stack := .pair (.boxedInt r.1.toUInt32) (.pair (.boxedInt r.2.1.toUInt32) (.boxedInt r.2.2.toUInt32)) :: rest })
      | none => .inr none
    | "f_Algorithm_life105Rest", .ext (.u64Ref accId) :: limit :: i :: minX :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]?, st.heap.u64Arrays[accId]? with
      | some cells, some acc =>
        let res := Algorithm.life105Rest cells minX.asI32.toInt32 i.asI32 limit.asI32 acc
        let newId := st.heap.u64Arrays.length
        .inl (some { st with
          pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
          heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [res] } })
      | _, _ => .inr none
    | "f_Algorithm_macroCellAt", i :: .heapRef nodesAddr :: rest =>
      match st.jvmHeap.get? nodesAddr with
      | some (.objArray _ elems) =>
        let nodesOpt := elems.foldlM (fun acc v => match v with | .ext (.mc m) => some (acc.push m) | _ => none) #[]
        match nodesOpt with
        | some nodes =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (Algorithm.macroCellAt nodes i.asI32)) :: rest })
        | none => .inr none
      | _ => .inr none
    | "f_Algorithm_macroCellWithCell", isAlive :: y :: x :: .ext (.mc m) :: rest =>
      .inl (some { st with
        pc := st.pc + 1,
        stack := .ext (.mc (Algorithm.macroCellWithCell m x.asI32.toInt32 y.asI32.toInt32 (isAlive.asI32 != 0))) :: rest })
    | "f_Algorithm_macrocellCellChild", id :: .ext (.mc emptySub) :: lvl :: isLeafVal :: nodesVal :: rest =>
      let nodes? : Option (Algorithm.GrowBuf Algorithm.MacroCell) := match nodesVal with
        | .ext (.mcGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      let isLeaf? : Option (Algorithm.GrowBuf Bool) := match isLeafVal with
        | .ext (.boolGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match nodes?, isLeaf? with
      | some nodes, some isLeaf =>
        let res := match Algorithm.macrocellCellChild nodes isLeaf lvl.asI32 emptySub id.asI32 with
          | some c => .ext (.mc c)
          | none => .null
        .inl (some { st with pc := st.pc + 1, stack := res :: rest })
      | _, _ => .inr none
    | "f_Algorithm_macrocellLeafChild", id :: isLeafVal :: leavesVal :: rest =>
      let leaves? : Option (Algorithm.GrowBuf UInt64) := match leavesVal with
        | .ext (.u64GrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      let isLeaf? : Option (Algorithm.GrowBuf Bool) := match isLeafVal with
        | .ext (.boolGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match leaves?, isLeaf? with
      | some leaves, some isLeaf =>
        let res := match Algorithm.macrocellLeafChild leaves isLeaf id.asI32 with
          | some v => .boxedULong v
          | none => .null
        .inl (some { st with pc := st.pc + 1, stack := res :: rest })
      | _, _ => .inr none
    | "f_Algorithm_macrocellLeafChild___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedULong 0 :: rest })
    | "f_Algorithm_macrocellSingleLeaf", .ext (.mc m) :: rest =>
      let res := match Algorithm.macrocellSingleLeaf m with | some v => .boxedULong v | none => .null
      .inl (some { st with pc := st.pc + 1, stack := res :: rest })
    | "f_Algorithm_macrocellSingleLeaf___lam__0", _p :: v :: rest
    | "f_Algorithm_macrocellSingleLeaf___lam__1", _p :: v :: rest
    | "f_Algorithm_macrocellSingleLeaf___lam__2", _p :: v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if v.asI64 == 0 then 1 else 0) :: rest })
    | "f_Algorithm_noCells", rest =>
      let newId := st.heap.u64Arrays.length
      .inl (some { st with
        pc := st.pc + 1, stack := .ext (.u64Ref newId) :: rest,
        heap := { st.heap with u64Arrays := st.heap.u64Arrays ++ [#[]] } })
    | "f_Algorithm_parseBlockHeader", bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        let optPair := (Algorithm.parseBlockHeader bytes).map fun r =>
          (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
        let (res, h') := encodeOptScalarPair st.jvmHeap optPair
        .inl (some { st with pc := st.pc + 1, stack := res :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_parseBlocks",
        .ext (.u64Ref cId) :: warnsVal :: rowIdx :: blockY :: blockX :: hasBlock ::
        p :: limit :: bytesVal :: inRow :: i :: numLines :: linesVal :: rest =>
      match decodeStrArray st linesVal, decodeBytes st bytesVal, st.heap.u64Arrays[cId]? with
      | some lines, some bytes, some cells =>
        let warnsOpt : Option (Array Algorithm.Life105Warning) := match warnsVal with
          | .strArr #[] => some #[]
          | .heapRef wAddr =>
            match st.jvmHeap.get? wAddr with
            | some (.objArray _ elems) => elems.foldlM (fun acc v => (decodeLife105Warning st.jvmHeap v).map acc.push) #[]
            | _ => none
          | _ => none
        match warnsOpt with
        | some warns =>
          let res := Algorithm.parseBlocks lines numLines.asI32 i.asI32 (inRow.asI32 != 0) bytes
            limit.asI32 p.asI32 (hasBlock.asI32 != 0) blockX.asI32.toInt32 blockY.asI32.toInt32
            rowIdx.asI32.toInt32 warns cells
          let (resVal, h', u64s') := encodeLife105Result st.jvmHeap st.heap.u64Arrays res
          .inl (some { st with
            pc := st.pc + 1, stack := resVal :: rest,
            jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
        | none => .inr none
      | _, _, _ => .inr none
    | "f_Algorithm_parseCoordLine", .str line :: rest =>
      let v := match Algorithm.parseCoordLine line with
        | some (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)
        | none => .null
      .inl (some { st with pc := st.pc + 1, stack := v :: rest })
    | "f_Algorithm_parseInt32At", limit :: pos :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        let optPair := (Algorithm.parseInt32At bytes pos.asI32 limit.asI32).map fun r =>
          (.boxedInt r.val.toUInt32, .boxedUInt r.next)
        let (res, h') := encodeOptScalarPair st.jvmHeap optPair
        .inl (some { st with pc := st.pc + 1, stack := res :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_parseMCNodeLine", bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        match Algorithm.parseMCNodeLine bytes with
        | none =>
          let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
        | some nl =>
          let inner : Array JvmVal := (Array.replicate 50 .null)
            |>.set! 0 (.boxedInt 0)
            |>.set! 1 (.boxedUInt nl.level)
            |>.set! 5 (.boxedUInt nl.nw)
            |>.set! 9 (.boxedUInt nl.nwStart)
            |>.set! 13 (.boxedUInt nl.nwEnd)
            |>.set! 17 (.boxedUInt nl.ne)
            |>.set! 21 (.boxedUInt nl.neStart)
            |>.set! 25 (.boxedUInt nl.neEnd)
            |>.set! 29 (.boxedUInt nl.sw)
            |>.set! 33 (.boxedUInt nl.swStart)
            |>.set! 37 (.boxedUInt nl.swEnd)
            |>.set! 41 (.boxedUInt nl.se)
            |>.set! 45 (.boxedUInt nl.seStart)
            |>.set! 49 (.boxedUInt nl.seEnd)
          let (innerAddr, h1) := st.jvmHeap.alloc (.objArray "java/lang/Object" inner)
          let (outerAddr, h2) := h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef outerAddr :: rest, jvmHeap := h2 })
      | none => .inr none
    | "f_Algorithm_parseRLEComments",
        warnsVal :: hasOffset :: offsetY :: offsetX :: i :: numLines :: linesVal :: rest =>
      let warns? : Option (Algorithm.GrowBuf Algorithm.RLEWarning) := match warnsVal with
        | .ext (.rleWarnGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match decodeStrArray st linesVal, warns? with
      | some lines, some warns =>
        let res := Algorithm.parseRLEComments lines numLines.asI32 i.asI32
          offsetX.asI32.toInt32 offsetY.asI32.toInt32 (hasOffset.asI32 != 0) warns
        let (resVal, h', u64s') := encodeRLEResult st.jvmHeap st.heap.u64Arrays res
        .inl (some { st with
          pc := st.pc + 1, stack := resVal :: rest,
          jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
      | _, _ => .inr none
    | "f_Algorithm_parseRLEComments___closed__1", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.rleStatus (.invalidHeader "none")) :: rest })
    | "f_Algorithm_parseRLEData",
        startY :: startX :: runsVal :: warnsVal :: countCol :: countP :: hasCount :: count ::
        col :: p :: limit :: bytesVal :: inLine :: i :: numLines :: linesVal :: rest =>
      let warns? : Option (Algorithm.GrowBuf Algorithm.RLEWarning) := match warnsVal with
        | .ext (.rleWarnGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      let runs? : Option (Algorithm.GrowBuf (UInt32 × UInt32)) := match runsVal with
        | .ext (.u32PairGrowBuf b) => some b
        | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none
      match decodeStrArray st linesVal, decodeBytes st bytesVal, warns?, runs? with
      | some lines, some bytes, some warns, some runs =>
        let res := Algorithm.parseRLEData lines numLines.asI32 i.asI32 (inLine.asI32 != 0)
          bytes limit.asI32 p.asI32 col.asI32 count.asI64 (hasCount.asI32 != 0) countP.asI32 countCol.asI32
          warns runs startX.asI32.toInt32 startY.asI32.toInt32
        let (resVal, h', u64s') := encodeRLEResult st.jvmHeap st.heap.u64Arrays res
        .inl (some { st with
          pc := st.pc + 1, stack := resVal :: rest,
          jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
      | _, _, _, _ => .inr none
    | "f_Algorithm_parseRLEData___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt 0) (.boxedUInt 1) :: rest })
    | "f_Algorithm_parseRLEData___closed__2", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_parseRLEHeader", bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.parseRLEHeader bytes) :: rest })
      | none => .inr none
    | "f_Algorithm_parseRLEHeader___lam__0", ch :: pos :: limit :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        let p' := Algorithm.skipSpaces bytes pos.asI32 limit.asI32
        let res :=
          if p' < limit.asI32 && bytes.data[p'.toNat]! == ch.asI32.toUInt8 then .boxedUInt (p' + 1)
          else .null
        .inl (some { st with pc := st.pc + 1, stack := res :: rest })
      | none => .inr none
    | "f_Algorithm_parseRLEHeader___lam__1", pos :: limit :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        let p' := Algorithm.skipSpaces bytes pos.asI32 limit.asI32
        let res := match Algorithm.parseUInt32At bytes p' limit.asI32 with
          | some r => .boxedUInt r.next
          | none => .null
        .inl (some { st with pc := st.pc + 1, stack := res :: rest })
      | none => .inr none
    | "f_Algorithm_parseRLEOffset", bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        let optPair := (Algorithm.parseRLEOffset bytes).map fun r =>
          (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
        let (res, h') := encodeOptScalarPair st.jvmHeap optPair
        .inl (some { st with pc := st.pc + 1, stack := res :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_parseUInt32At", limit :: pos :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        let optPair := (Algorithm.parseUInt32At bytes pos.asI32 limit.asI32).map fun r =>
          (.boxedUInt r.val, .boxedUInt r.next)
        let (res, h') := encodeOptScalarPair st.jvmHeap optPair
        .inl (some { st with pc := st.pc + 1, stack := res :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_Algorithm_relativeKeysLoop", accVal :: minY :: minX :: limit :: i :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]?, decodeU64List st.jvmHeap (st.jvmHeap.objects.size + 2) accVal with
      | some cells, some acc =>
        let res := Algorithm.relativeKeysLoop cells i.asI32 limit.asI32 minX.asI64 minY.asI64 acc
        let (resVal, h') := encodeU64List st.jvmHeap res
        .inl (some { st with pc := st.pc + 1, stack := resVal :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "f_Algorithm_scanDigitSet", mask :: p :: limit :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        let r := Algorithm.scanDigitSet bytes limit.asI32 p.asI32 mask.asI32
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest })
      | none => .inr none
    | "f_Algorithm_scanDigits", acc :: p :: limit :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        let r := Algorithm.scanDigits ⟨elems⟩ limit.asI32 p.asI32 acc.asI64
        .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.boxedULong r.2) :: rest })
      | _ => .inr none
    | "f_Algorithm_serializeLife105Block", maxY :: minY :: minX :: .ext (.u64Ref cId) :: rest =>
      match st.heap.u64Arrays[cId]? with
      | some cells =>
        let arr := Algorithm.serializeLife105Block cells minX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32
        .inl (some { st with pc := st.pc + 1, stack := .strArr arr :: rest })
      | none => .inr none
    | "f_Algorithm_serializeMacrocell___closed__2", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[.str "[M2] (ComposeLife 1.0)"])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_serializeRLE___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUByte 33) (.boxedUInt 1) :: rest })
    | "f_Algorithm_serializeRLE___closed__3", rest =>
      let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object"
        #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23", .str "!"])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "f_Algorithm_skipDescriptions", i :: numLines :: linesVal :: rest =>
      match decodeStrArray st linesVal with
      | some lines =>
        .inl (some { st with
          pc := st.pc + 1, stack := .i32 (Algorithm.skipDescriptions lines numLines.asI32 i.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_skipSpaces", limit :: pos :: bytesVal :: rest =>
      match decodeBytes st bytesVal with
      | some bytes =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.skipSpaces bytes pos.asI32 limit.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_splitKeys", seVal :: swVal :: neVal :: nwVal :: midY :: midX :: keysVal :: rest =>
      let fuel := st.jvmHeap.objects.size + 2
      match decodeU64List st.jvmHeap fuel keysVal,
            decodeU64List st.jvmHeap fuel nwVal,
            decodeU64List st.jvmHeap fuel neVal,
            decodeU64List st.jvmHeap fuel swVal,
            decodeU64List st.jvmHeap fuel seVal with
      | some keys, some nw, some ne, some sw, some se =>
        let r := Algorithm.splitKeys keys midX.asI64 midY.asI64 nw ne sw se
        let (nwV, h1) := encodeU64List st.jvmHeap r.1
        let (neV, h2) := encodeU64List h1 r.2.1
        let (swV, h3) := encodeU64List h2 r.2.2.1
        let (seV, h4) := encodeU64List h3 r.2.2.2
        .inl (some { st with
          pc := st.pc + 1,
          stack := .pair nwV (.pair neV (.pair swV seV)) :: rest,
          jvmHeap := h4 })
      | _, _, _, _, _ => .inr none
    | "f_Algorithm_uint32ToInt32", x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 x.asI32 :: rest })
    | "f_Algorithm_wrapRLEItems",
        .ext (.strGrowBuf out) :: lineLen :: .str line :: j :: numItems :: .heapRef itemsAddr :: rest =>
      match st.jvmHeap.get? itemsAddr with
      | some (.objArray _ elems) =>
        let itemsOpt := elems.foldlM (fun acc v => match v with
          | .pair a b => some (acc.push (unboxU8 a, unboxI32 b))
          | _ => none) #[]
        match itemsOpt with
        | some items =>
          let r := Algorithm.wrapRLEItems items numItems.asI32 j.asI32 line lineLen.asI32 out
          .inl (some { st with pc := st.pc + 1, stack := .ext (.strGrowBuf r) :: rest })
        | none => .inr none
      | _ => .inr none
    | "f_Algorithm_wrapRLEItems___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUByte 0) (.boxedUInt 0) :: rest })
    | "f_Algorithm_writeDag", wVal :: .ext (.u64Ref idsId) :: n :: k :: .heapRef kidsAddr :: .heapRef entriesAddr :: rest =>
      match st.jvmHeap.get? entriesAddr, st.jvmHeap.get? kidsAddr, st.heap.u64Arrays[idsId]? with
      | some (.objArray _ eElems), some (.intArray kids), some ids =>
        let entriesOpt := eElems.foldlM (fun acc v => match v with | .ext (.mc m) => some (acc.push m) | _ => none) #[]
        match entriesOpt with
        | some entries =>
          match wVal with
          | .ext (.dagWriter w) =>
            let w' := Algorithm.writeDag entries kids k.asI32 n.asI32 ids w
            .inl (some { st with pc := st.pc + 1, stack := .ext (.dagWriter w') :: rest })
          | _ =>
            match decodeDagWriter st.jvmHeap wVal with
            | some w =>
              let w' := Algorithm.writeDag entries kids k.asI32 n.asI32 ids w
              let (wVal', h') := encodeDagWriter st.jvmHeap w'
              .inl (some { st with pc := st.pc + 1, stack := wVal' :: rest, jvmHeap := h' })
            | none => .inr none
        | none => .inr none
      | _, _, _ => .inr none
    | "f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg", listVal :: k :: rest =>
      match decodeLeafBucketList st.jvmHeap (st.jvmHeap.objects.size + 2) listVal with
      | some lst =>
        match lst.lookup k.asI64 with
        | none =>
          let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
        | some v =>
          let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
    | "f_List_lookup___at___00Algorithm_MacrocellWriterState_addNode_spec__0___redArg", listVal :: kVal :: rest =>
      match decodeNodeKey kVal, decodeNodeBucketList st.jvmHeap (st.jvmHeap.objects.size + 2) listVal with
      | some k, some lst =>
        match lst.lookup k with
        | none =>
          let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
        | some v =>
          let (addr, h') := st.jvmHeap.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "getEMPTY_LEVEL_4", rest =>
      let v := (st.jvmHeap.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4").getD (.ext (.mc Algorithm.emptyLevel4))
      .inl (some { st with pc := st.pc + 1, stack := v :: rest })
    | "getEMPTY_NODES", rest =>
      match st.jvmHeap.getStatic? "MacroCellLeanKt" "EMPTY_NODES" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "getNEXT_GEN_4X4_LUT", rest =>
      match st.jvmHeap.getStatic? "AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | _, _ => .inr none

def algStepInvokeInterface (st : JvmState) (cls method _desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, st.stack with
  | "kotlin/jvm/functions/Function1", "invoke", arg :: .ext fn :: rest =>
    match fn, arg with
    | .fnU64ToU32 f, .boxedULong v =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt (f v) :: rest })
    | .fnU64ToU32 f, .i64 v =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt (f v) :: rest })
    | .fnMcToU64 f, .ext (.mc m) =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedULong (f m) :: rest })
    | .fnMcToMc f, .ext (.mc m) =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.mc (f m)) :: rest })
    | .fnMcToOptMc f, .ext (.mc m) =>
      let res := match f m with | some c => .ext (.mc c) | none => .null
      .inl (some { st with pc := st.pc + 1, stack := res :: rest })
    | .fnHlToHl f, .ext (.hlState hs) =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.hlState (f hs)) :: rest })
    | _, _ => .inr none
  | _, _, _ => .inr none

abbrev algHooks : Jvm.JvmHooks AlgExt AlgHeap where
  checkInstanceOf := checkInstanceOf
  checkCast := checkCast
  isSubtypeOf := isSubtypeOf
  resolveStatic := algResolveStatic
  stepInvokeVirtual := algStepInvokeVirtual
  stepInvokeSpecial := algStepInvokeSpecial
  stepInvokeStatic := algStepInvokeStatic
  stepInvokeInterface := algStepInvokeInterface

@[inline] def stepInvokeVirtual (st : JvmState) (cls method desc : String) : Option JvmState ⊕ Option JvmVal :=
  Jvm.stepInstr algHooks (.invokevirtual cls method desc) st

@[inline] def stepInvokeSpecial (st : JvmState) (cls method desc : String) : Option JvmState ⊕ Option JvmVal :=
  Jvm.stepInstr algHooks (.invokespecial cls method desc) st

@[inline] def stepInvokeStatic (st : JvmState) (cls method desc : String) : Option JvmState ⊕ Option JvmVal :=
  Jvm.stepInstr algHooks (.invokestatic cls method desc) st

@[inline] def stepInvokeInterface (st : JvmState) (cls method desc : String) : Option JvmState ⊕ Option JvmVal :=
  Jvm.stepInstr algHooks (.invokeinterface cls method desc) st

abbrev stepInstr (instr : JvmInstr) (st : JvmState) : Option JvmState ⊕ Option JvmVal :=
  Jvm.stepInstr algHooks instr st

abbrev runJvm (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.runJvm algHooks fuel prog st

abbrev runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  Jvm.runJvmRes algHooks fuel prog st

end Algorithm.JvmVerification
