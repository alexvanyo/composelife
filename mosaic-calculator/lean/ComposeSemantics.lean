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

namespace MosaicCalculator.Compose

/-- Model of a Compose restart group stored in the slot table, parameterized by slot value type `Val`. -/
structure GroupEntry (Val : Type) where
  key : Int32
  slots : List Val := []
  dirty : Bool := false
  reads : List Nat := []
  restartClosure? : Option Val := none
  deriving Repr, Inhabited

/-- Active restart-group frame maintained while executing a `@Composable` function body. -/
structure ActiveGroupFrame where
  key : Int32
  cursor : Nat := 0
  lastReadIdx? : Option Nat := none
  inDefaults : Bool := false
  skipped : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Compose slot table + active group cursor + snapshot MutableState cell store. -/
structure ComposerModel (Val : Type) where
  inserting : Bool := true
  groups : List (GroupEntry Val) := []
  groupStack : List ActiveGroupFrame := []
  stateCells : List (Nat × Val) := []
  nextStateId : Nat := 0
  traceEnabled : Bool := false
  deriving Repr, Inhabited

def ComposerModel.initial {Val : Type} (inserting : Bool := true) : ComposerModel Val :=
  { inserting := inserting }

private def listSetAt {α : Type} : List α → Nat → α → List α
  | [], 0, v => [v]
  | [], n + 1, v => v :: listSetAt [] n v
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSetAt xs n v

private def upsertGroup {Val : Type} (k : Int32) : List (GroupEntry Val) → List (GroupEntry Val)
  | [] => [{ key := k }]
  | g :: gs => if g.key == k then g :: gs else g :: upsertGroup k gs

private def updateGroup {Val : Type} (k : Int32) (f : GroupEntry Val → GroupEntry Val) :
    List (GroupEntry Val) → List (GroupEntry Val)
  | [] => []
  | g :: gs => if g.key == k then f g :: gs else g :: updateGroup k f gs

private def findGroup? {Val : Type} (k : Int32) : List (GroupEntry Val) → Option (GroupEntry Val)
  | [] => none
  | g :: gs => if g.key == k then some g else findGroup? k gs

/-- Enter a restart group (`Composer.startRestartGroup`). -/
def startRestartGroup {Val : Type} (m : ComposerModel Val) (key : Int32) : ComposerModel Val :=
  let groups' := upsertGroup key m.groups
  let frame : ActiveGroupFrame := { key := key, cursor := 0 }
  { m with groups := groups', groupStack := frame :: m.groupStack }

/-- Current group entry on top of the active stack, if any. -/
def currentGroup? {Val : Type} (m : ComposerModel Val) : Option (GroupEntry Val) :=
  match m.groupStack with
  | f :: _ => findGroup? f.key m.groups
  | [] => none

/-- Compute `Composer.shouldExecute(parametersChanged, flags)`. -/
def shouldExecute {Val : Type} (m : ComposerModel Val) (parametersChanged : Bool) (_flags : Int32) : Bool :=
  if m.inserting || parametersChanged then true
  else
    match currentGroup? m with
    | some g => g.dirty
    | none => false

/-- Enter defaults sub-phase (`Composer.startDefaults`). -/
def startDefaults {Val : Type} (m : ComposerModel Val) : ComposerModel Val :=
  match m.groupStack with
  | f :: rest => { m with groupStack := { f with inDefaults := true } :: rest }
  | [] => m

/-- Query `Composer.getDefaultsInvalid`. -/
def getDefaultsInvalid {Val : Type} (m : ComposerModel Val) : Bool :=
  m.inserting

/-- Leave defaults sub-phase (`Composer.endDefaults`). -/
def endDefaults {Val : Type} (m : ComposerModel Val) : ComposerModel Val :=
  match m.groupStack with
  | f :: rest => { m with groupStack := { f with inDefaults := false } :: rest }
  | [] => m

/-- Skip remaining composition in defaults or body (`Composer.skipToGroupEnd`). -/
def skipToGroupEnd {Val : Type} (m : ComposerModel Val) : ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    if f.inDefaults then m
    else { m with groupStack := { f with skipped := true } :: rest }
  | [] => m

/-- Exit current restart group (`Composer.endRestartGroup`) and return `(groupKey?, updatedComposer)`. -/
def endRestartGroup {Val : Type} (m : ComposerModel Val) : Option Int32 × ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    let groups' := updateGroup f.key (fun g => { g with dirty := false }) m.groups
    (some f.key, { m with groups := groups', groupStack := rest })
  | [] => (none, m)

/-- Attach restart closure to a group (`ScopeUpdateScope.updateScope`). -/
def setGroupRestartClosure {Val : Type} (m : ComposerModel Val) (key : Int32) (closure : Val) :
    ComposerModel Val :=
  { m with groups := updateGroup key (fun g => { g with restartClosure? := some closure }) m.groups }

/-- Check and update a `changed`/`changedInstance` slot; returns `(hasChanged, updatedComposer)`. -/
def checkChangedSlot {Val : Type} [Inhabited Val] (beqVal : Val → Val → Bool)
    (m : ComposerModel Val) (newVal : Val) : Bool × ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    match findGroup? f.key m.groups with
    | some g =>
      match g.slots[f.cursor]? with
      | some oldVal =>
        let changed := !(beqVal oldVal newVal)
        let slots' := listSetAt g.slots f.cursor newVal
        let groups' := updateGroup f.key (fun g0 => { g0 with slots := slots' }) m.groups
        let f' := { f with cursor := f.cursor + 1 }
        (changed, { m with groups := groups', groupStack := f' :: rest })
      | none =>
        let slots' := g.slots ++ [newVal]
        let groups' := updateGroup f.key (fun g0 => { g0 with slots := slots' }) m.groups
        let f' := { f with cursor := f.cursor + 1 }
        (true, { m with groups := groups', groupStack := f' :: rest })
    | none => (true, m)
  | [] => (true, m)

/-- Read current remember slot (`Composer.rememberedValue`), returning `none` when uninitialized (`Composer.Empty`). -/
def readRememberSlot {Val : Type} (m : ComposerModel Val) : Option Val × ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    match findGroup? f.key m.groups with
    | some g =>
      let idx := f.cursor
      let val? := g.slots[idx]?
      let f' := { f with cursor := idx + 1, lastReadIdx? := some idx }
      (val?, { m with groupStack := f' :: rest })
    | none => (none, m)
  | [] => (none, m)

/-- Update the slot most recently read by `readRememberSlot` (`Composer.updateRememberedValue`). -/
def writeRememberSlot {Val : Type} (m : ComposerModel Val) (val : Val) : ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    match f.lastReadIdx?, findGroup? f.key m.groups with
    | some idx, some g =>
      let slots' :=
        if idx < g.slots.length then listSetAt g.slots idx val
        else g.slots ++ [val]
      let groups' := updateGroup f.key (fun g0 => { g0 with slots := slots' }) m.groups
      { m with groups := groups', groupStack := { f with lastReadIdx? := none } :: rest }
    | _, _ => m
  | [] => m

/-- Allocate a new snapshot `MutableState` cell (`SnapshotStateKt.mutableStateOf$default`). -/
def allocMutableState {Val : Type} (m : ComposerModel Val) (initial : Val) : Nat × ComposerModel Val :=
  let stateId := m.nextStateId
  let cells' := (stateId, initial) :: m.stateCells
  (stateId, { m with stateCells := cells', nextStateId := stateId + 1 })

private def recordReadInActiveGroups {Val : Type} (stateId : Nat) :
    List ActiveGroupFrame → List (GroupEntry Val) → List (GroupEntry Val)
  | [], gs => gs
  | f :: fs, gs =>
    let gs' := updateGroup f.key
      (fun g => if stateId ∈ g.reads then g else { g with reads := stateId :: g.reads }) gs
    recordReadInActiveGroups stateId fs gs'

/-- Read `MutableState.getValue`, recording a snapshot read dependency in active groups. -/
def readMutableState {Val : Type} (m : ComposerModel Val) (stateId : Nat) :
    Option (Val × ComposerModel Val) :=
  match m.stateCells.find? (fun (id, _) => id == stateId) with
  | some (_, v) =>
    let groups' := recordReadInActiveGroups stateId m.groupStack m.groups
    some (v, { m with groups := groups' })
  | none => none

/-- Write `MutableState.setValue`, marking reader groups dirty when structurally changed. -/
def writeMutableState {Val : Type} (beqVal : Val → Val → Bool)
    (m : ComposerModel Val) (stateId : Nat) (newVal : Val) : Option (ComposerModel Val) :=
  match m.stateCells.find? (fun (id, _) => id == stateId) with
  | some (_, oldVal) =>
    if beqVal oldVal newVal then some m
    else
      let cells' := m.stateCells.map fun (id, v) => if id == stateId then (id, newVal) else (id, v)
      let groups' := m.groups.map fun g => if stateId ∈ g.reads then { g with dirty := true } else g
      some { m with stateCells := cells', groups := groups' }
  | none => none

/-- Prepare the composer for a recomposition pass (`inserting := false`, reset stack). -/
def beginRecompose {Val : Type} (m : ComposerModel Val) : ComposerModel Val :=
  { m with inserting := false, groupStack := [] }

/-- Replay the root restart closure after invalidation, if registered. -/
def rootRestartClosure? {Val : Type} (m : ComposerModel Val) : Option Val :=
  m.groups.findSome? (·.restartClosure?)

/-- Mirror Compose `RecomposeScopeImplKt.updateChangedFlags` bit scrambling. -/
def updateChangedFlags (flags : UInt32) : UInt32 :=
  let lowMask : UInt32 := 0x12492492
  let highMask : UInt32 := 0x24924924
  let lowBits := flags &&& lowMask
  let highBits := flags &&& highMask
  (flags &&& (~~~(lowBits ||| highBits))) ||| (highBits >>> 1) ||| (lowBits <<< 1)

end MosaicCalculator.Compose
