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

namespace MosaicCalculator.Model

inductive CalculatorOp where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr, Inhabited

def CalculatorOp.symbol : CalculatorOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"

inductive CalculatorError where
  | divideByZero
  | overflow
  deriving DecidableEq, Repr, Inhabited

inductive CalculatorKey where
  | digit (d : UInt32)
  | op (o : CalculatorOp)
  | equals
  | clear
  | backspace
  deriving DecidableEq, Repr, Inhabited

structure CalculatorState where
  displayValue : Int64 := 0
  pendingOperand : Option Int64 := none
  pendingOp : Option CalculatorOp := none
  enteringNewNumber : Bool := true
  error : Option CalculatorError := none
  deriving DecidableEq, Repr, Inhabited

def CalculatorState.initial : CalculatorState := {}

inductive CheckedEvalResult where
  | value (v : Int64)
  | error (e : CalculatorError)
  deriving DecidableEq, Repr, Inhabited

def int64Min : Int64 := (-9223372036854775808 : Int).toInt64

/-- Signed 64-bit JVM `ladd` overflow check matching `(a ^ res) & (b ^ res) < 0`. -/
def checkedAddModel (a b : Int64) : CheckedEvalResult :=
  let res : UInt64 := a.toUInt64 + b.toUInt64
  if (((a.toUInt64 ^^^ res) &&& (b.toUInt64 ^^^ res)).toBitVec.slt 0#64) then
    .error .overflow
  else
    .value res.toInt64

/-- Signed 64-bit JVM `lsub` overflow check matching `(a ^ b) & (a ^ res) < 0`. -/
def checkedSubModel (a b : Int64) : CheckedEvalResult :=
  let res : UInt64 := a.toUInt64 - b.toUInt64
  if (((a.toUInt64 ^^^ b.toUInt64) &&& (a.toUInt64 ^^^ res)).toBitVec.slt 0#64) then
    .error .overflow
  else
    .value res.toInt64

/-- Two's-complement signed 64-bit JVM `ldiv` quotient. -/
def jvmI64Div (a b : Int64) : Int64 :=
  (BitVec.sdiv a.toBitVec b.toBitVec).toInt.toInt64

/-- Signed 64-bit checked multiplication matching `checkedMul`. -/
def checkedMulModel (a b : Int64) : CheckedEvalResult :=
  if a == 0 || b == 0 then .value 0
  else if (a == int64Min && b == -1) || (b == int64Min && a == -1) then .error .overflow
  else
    let res : Int64 := (a.toUInt64 * b.toUInt64).toInt64
    if jvmI64Div res b != a then .error .overflow else .value res

/-- Signed 64-bit checked division matching `checkedDiv`. -/
def checkedDivModel (a b : Int64) : CheckedEvalResult :=
  if b == 0 then .error .divideByZero
  else if a == int64Min && b == -1 then .error .overflow
  else .value (jvmI64Div a b)

def applyOpModel (lhs : Int64) (op : CalculatorOp) (rhs : Int64) : CheckedEvalResult :=
  match op with
  | .add => checkedAddModel lhs rhs
  | .sub => checkedSubModel lhs rhs
  | .mul => checkedMulModel lhs rhs
  | .div => checkedDivModel lhs rhs

def reduceCalculatorStateModel (state : CalculatorState) (key : CalculatorKey) : CalculatorState :=
  match key with
  | .clear => CalculatorState.initial
  | _ =>
    if state.error.isSome then state
    else
      match key with
      | .digit d =>
        let dl : Int64 := (Int32.ofInt d.toBitVec.toInt).toInt64
        if state.enteringNewNumber then
          { state with displayValue := dl, enteringNewNumber := false }
        else
          match checkedMulModel state.displayValue 10 with
          | .error e => { state with error := some e }
          | .value mul =>
            let next :=
              if state.displayValue.toBitVec.slt 0#64 then checkedSubModel mul dl
              else checkedAddModel mul dl
            match next with
            | .error e => { state with error := some e }
            | .value v => { state with displayValue := v }
      | .backspace =>
        if state.enteringNewNumber then state
        else { state with displayValue := jvmI64Div state.displayValue 10 }
      | .op o =>
        match state.pendingOperand, state.pendingOp with
        | some lhs, some op =>
          if !state.enteringNewNumber then
            match applyOpModel lhs op state.displayValue with
            | .error e =>
              { state with pendingOperand := none, pendingOp := none, enteringNewNumber := true, error := some e }
            | .value v =>
              { state with displayValue := v, pendingOperand := some v, pendingOp := some o, enteringNewNumber := true }
          else
            { state with pendingOperand := some state.displayValue, pendingOp := some o, enteringNewNumber := true }
        | _, _ =>
          { state with pendingOperand := some state.displayValue, pendingOp := some o, enteringNewNumber := true }
      | .equals =>
        match state.pendingOperand, state.pendingOp with
        | some lhs, some op =>
          match applyOpModel lhs op state.displayValue with
          | .error e => { error := some e }
          | .value v => { displayValue := v }
        | _, _ => { state with enteringNewNumber := true }
      | .clear => CalculatorState.initial

def mapTerminalKeyModel (key : String) : Option CalculatorKey :=
  match key with
  | "0" => some (.digit 0)
  | "1" => some (.digit 1)
  | "2" => some (.digit 2)
  | "3" => some (.digit 3)
  | "4" => some (.digit 4)
  | "5" => some (.digit 5)
  | "6" => some (.digit 6)
  | "7" => some (.digit 7)
  | "8" => some (.digit 8)
  | "9" => some (.digit 9)
  | "+" => some (.op .add)
  | "-" => some (.op .sub)
  | "*" => some (.op .mul)
  | "/" => some (.op .div)
  | "=" | "Enter" => some .equals
  | "c" | "C" | "Escape" => some .clear
  | "Backspace" => some .backspace
  | _ => none

def int64ToString (v : Int64) : String :=
  toString v.toInt

def formatDisplayLineModel (state : CalculatorState) : String :=
  match state.error with
  | some .divideByZero => "ERR: DIV BY ZERO"
  | some .overflow => "ERR: OVERFLOW"
  | none =>
    match state.pendingOperand, state.pendingOp with
    | some lhs, some op =>
      if state.enteringNewNumber then s!"{int64ToString lhs} {op.symbol}"
      else s!"{int64ToString lhs} {op.symbol} {int64ToString state.displayValue}"
    | _, _ => int64ToString state.displayValue

def expectedCalculatorScreenLines (state : CalculatorState) : List String :=
  [ "=== Calculator ==="
  , s!"> {formatDisplayLineModel state}"
  , "[7] [8] [9] [/]"
  , "[4] [5] [6] [*]"
  , "[1] [2] [3] [-]"
  , "[0] [C] [=] [+]"
  ]

def expectedCalculatorScreen (state : CalculatorState) : String :=
  String.intercalate "\n" (expectedCalculatorScreenLines state)

end MosaicCalculator.Model
