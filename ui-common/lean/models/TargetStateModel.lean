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

namespace UiCommon.Model

/--
Pure Lean 4 model of `com.alexvanyo.composelife.ui.util.TargetState<T, M>`.
`Single(current)` represents a settled state; `InProgress(current, provisional, progress, metadata)`
represents an ongoing transition between `current` and `provisional`.
-/
inductive TargetState (α μ : Type) where
  | single (current : α)
  | inProgress (current provisional : α) (progress : Float32) (metadata : μ)

instance {α μ : Type} [Inhabited α] : Inhabited (TargetState α μ) :=
  ⟨.single default⟩

/-- Semantic `current` state of a `TargetState`. -/
def TargetState.current {α μ : Type} : TargetState α μ → α
  | .single c => c
  | .inProgress c _ _ _ => c

/-- `TargetState.isInProgress()`: `false` for `Single`, `true` for `InProgress`. -/
def TargetState.isInProgress {α μ : Type} : TargetState α μ → Bool
  | .single _ => false
  | .inProgress _ _ _ _ => true

/--
Guarded `TargetState.InProgress` constructor matching `init { require(current != provisional) }`.
Returns `none` (corresponding to throwing `IllegalArgumentException`) iff `current == provisional`.
-/
def TargetState.mkInProgress? {α μ : Type} [BEq α]
    (current provisional : α) (progress : Float32) (metadata : μ) : Option (TargetState α μ) :=
  if current == provisional then none
  else some (.inProgress current provisional progress metadata)

/-- Convenience `InProgress.Companion.invoke` with `Unit` metadata. -/
def TargetState.mkInProgressUnit? {α : Type} [BEq α]
    (current provisional : α) (progress : Float32) : Option (TargetState α Unit) :=
  TargetState.mkInProgress? current provisional progress ()

/--
Exact IEEE-754 `Float32` model of `TargetState<Boolean, *>.progressToTrue`:
- `InProgress`: `if provisional then progress else 1.0f - progress`
- `Single`: `if current then 1.0f else 0.0f`
-/
def TargetState.progressToTrue {μ : Type} : TargetState Bool μ → Float32
  | .inProgress _ provisional progress _ =>
    if provisional then progress else (1.0 : Float32) - progress
  | .single current =>
    if current then (1.0 : Float32) else (0.0 : Float32)

/-- Unchecked structural `TargetState.map` matching `TargetState<T, M>.map(lambda)`. -/
def TargetState.map {α β μ : Type} (f : α → β) : TargetState α μ → TargetState β μ
  | .single c => .single (f c)
  | .inProgress c p pr m => .inProgress (f c) (f p) pr m

/--
Guarded `TargetState.map` enforcing the `InProgress` `require(current != provisional)` invariant
on the mapped target values.
-/
def TargetState.mapChecked? {α β μ : Type} [BEq β] (f : α → β) :
    TargetState α μ → Option (TargetState β μ)
  | .single c => some (.single (f c))
  | .inProgress c p pr m => TargetState.mkInProgress? (f c) (f p) pr m

/-- `TargetState<Boolean, M>.not()` defined via `map Bool.not`. -/
def TargetState.not {μ : Type} (s : TargetState Bool μ) : TargetState Bool μ :=
  s.map Bool.not

/-- `TargetState<Boolean, M>.and(value)`. -/
def TargetState.and {μ : Type} (s : TargetState Bool μ) (value : Bool) : TargetState Bool μ :=
  if value then s else .single false

/-- `TargetState<Boolean, M>.or(value)`. -/
def TargetState.or {μ : Type} (s : TargetState Bool μ) (value : Bool) : TargetState Bool μ :=
  if value then .single true else s

/-- Well-formedness invariant of `TargetState`: `InProgress` requires `current ≠ provisional`. -/
def TargetState.IsValid {α μ : Type} : TargetState α μ → Prop
  | .single _ => True
  | .inProgress c p _ _ => c ≠ p

/-- Structural equality on `TargetState` matching Kotlin `data class` `equals` (`Float.compare`). -/
def floatBitEq (a b : Float32) : Bool :=
  (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits) ==
    (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits)

def TargetState.beq {α μ : Type} [BEq α] [BEq μ] : TargetState α μ → TargetState α μ → Bool
  | .single a, .single b => a == b
  | .inProgress c1 p1 pr1 m1, .inProgress c2 p2 pr2 m2 =>
    c1 == c2 && p1 == p2 && floatBitEq pr1 pr2 && m1 == m2
  | _, _ => false

end UiCommon.Model
