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

namespace ResourceState.Model

/-- Model of JVM `Throwable` including `CompositeException` wrapping `List ThrowableModel`. -/
inductive ThrowableModel where
  | named (name : String)
  | composite (exceptions : List ThrowableModel)
  deriving Inhabited

mutual
  private def reprThrowable : ThrowableModel → Nat → Std.Format
    | .named n, p => Repr.addAppParen (f!"ThrowableModel.named {repr n}") p
    | .composite xs, p => Repr.addAppParen (f!"ThrowableModel.composite [{reprThrowableList xs}]") p

  private def reprThrowableList : List ThrowableModel → Std.Format
    | [] => ""
    | [x] => reprThrowable x 0
    | x :: xs => reprThrowable x 0 ++ ", " ++ reprThrowableList xs
end

instance : Repr ThrowableModel where
  reprPrec := reprThrowable

mutual
  private def decEqThrowable : (a b : ThrowableModel) → Decidable (a = b)
    | .named a, .named b =>
      if h : a = b then isTrue (by subst h; rfl)
      else isFalse (by intro h'; cases h'; exact h rfl)
    | .composite as, .composite bs =>
      match decEqThrowableList as bs with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .named _, .composite _ => isFalse (by intro h; cases h)
    | .composite _, .named _ => isFalse (by intro h; cases h)

  private def decEqThrowableList : (as bs : List ThrowableModel) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs =>
      match decEqThrowable a b, decEqThrowableList as bs with
      | isTrue ha, isTrue hb => isTrue (by subst ha; subst hb; rfl)
      | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
      | _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
end

instance : DecidableEq ThrowableModel := decEqThrowable

def ThrowableModel.message : ThrowableModel → String
  | .named n => n
  | .composite exns => s!"{exns.length} exceptions occurred."

def ThrowableModel.cause? : ThrowableModel → Option ThrowableModel
  | .named _ => none
  | .composite exns => exns.head?

/-- Sealed resource state matching `ResourceState<T>` (`Loading`, `Success`, `Failure`). -/
inductive ResourceState (α : Type) where
  | loading
  | success (value : α)
  | failure (throwable : ThrowableModel)
  deriving DecidableEq, Repr, Inhabited

def ResourceState.isLoading {α : Type} : ResourceState α → Bool
  | .loading => true
  | .success _ => false
  | .failure _ => false

def ResourceState.isSuccess {α : Type} : ResourceState α → Bool
  | .loading => false
  | .success _ => true
  | .failure _ => false

def ResourceState.isFailure {α : Type} : ResourceState α → Bool
  | .loading => false
  | .success _ => false
  | .failure _ => true

def ResourceState.map {α β : Type} (f : α → β) : ResourceState α → ResourceState β
  | .loading => .loading
  | .success v => .success (f v)
  | .failure t => .failure t

def ResourceState.flatMap {α β : Type} (f : α → ResourceState β) : ResourceState α → ResourceState β
  | .loading => .loading
  | .success v => f v
  | .failure t => .failure t

def extractFailures {α : Type} (states : List (ResourceState α)) : List ThrowableModel :=
  states.filterMap fun
    | .failure t => some t
    | _ => none

def hasLoading {α : Type} (states : List (ResourceState α)) : Bool :=
  states.any fun
    | .loading => true
    | _ => false

def extractSuccesses {α : Type} (states : List (ResourceState α)) : List α :=
  states.filterMap fun
    | .success v => some v
    | _ => none

/-- Vararg `combine` semantics: failure(s) > loading > all success. -/
def combineMany {α β : Type} (states : List (ResourceState α)) (transform : List α → β) :
    ResourceState β :=
  match extractFailures states with
  | [t] => .failure t
  | ts@(_ :: _ :: _) => .failure (.composite ts)
  | [] =>
    if hasLoading states then .loading
    else .success (transform (extractSuccesses states))

/-- Two-argument `combine` matching `combine(resourceState1, resourceState2, transform)`. -/
def combine2 {α β γ : Type} (r1 : ResourceState α) (r2 : ResourceState β)
    (transform : α → β → γ) : ResourceState γ :=
  match r1, r2 with
  | .failure t1, .failure t2 => .failure (.composite [t1, t2])
  | .failure t1, _ => .failure t1
  | _, .failure t2 => .failure t2
  | .loading, _ => .loading
  | _, .loading => .loading
  | .success a, .success b => .success (transform a b)

/-- Three-argument `combine` matching `combine(resourceState1, resourceState2, resourceState3, transform)`. -/
def combine3 {α β γ δ : Type} (r1 : ResourceState α) (r2 : ResourceState β)
    (r3 : ResourceState γ) (transform : α → β → γ → δ) : ResourceState δ :=
  let failures : List ThrowableModel :=
    (match r1 with | .failure t => [t] | _ => []) ++
    (match r2 with | .failure t => [t] | _ => []) ++
    (match r3 with | .failure t => [t] | _ => [])
  match failures with
  | [t] => .failure t
  | ts@(_ :: _ :: _) => .failure (.composite ts)
  | [] =>
    match r1, r2, r3 with
    | .success a, .success b, .success c => .success (transform a b c)
    | _, _, _ => .loading

/-- Finite trace model of a cold/hot `Flow<α>` with optional terminal exception. -/
structure FlowTrace (α : Type) where
  emissions : List α := []
  terminalFailure? : Option ThrowableModel := none
  deriving DecidableEq, Repr, Inhabited

/-- Model of `Flow<ResourceState<T>>.successes()`. -/
def successesFlow {α : Type} (flow : FlowTrace (ResourceState α)) :
    FlowTrace (ResourceState α) :=
  {
    emissions := flow.emissions.filterMap fun
      | .success v => some (.success v)
      | _ => none
    terminalFailure? := flow.terminalFailure?
  }

/-- Model of `Flow<ResourceState<T>>.firstSuccess()`. -/
def firstSuccessModel {α : Type} (flow : FlowTrace (ResourceState α)) :
    Option (ResourceState α) :=
  (successesFlow flow).emissions.head?

/-- Model of `Flow<T>.asResourceState()`. -/
def asResourceStateFlow {α : Type} (flow : FlowTrace α) : FlowTrace (ResourceState α) :=
  let mapped := flow.emissions.map ResourceState.success
  match flow.terminalFailure? with
  | some t => { emissions := mapped ++ [.failure t], terminalFailure? := none }
  | none => { emissions := mapped, terminalFailure? := none }

/-- Model of `Flow<ResourceState<T>>.collectAsState()` with initial value `Loading`. -/
def collectAsStateModel {α : Type} (flow : FlowTrace (ResourceState α)) :
    ResourceState α :=
  flow.emissions.getLast?.getD .loading

end ResourceState.Model
