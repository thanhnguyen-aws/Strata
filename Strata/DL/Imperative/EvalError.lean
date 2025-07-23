/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/



import Strata.DL.Imperative.PureExpr

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

/--
`EvalError` denotes the kinds of errors that may arise during (partial)
evaluation of Imperative programs.
-/
inductive EvalError (P : PureExpr) where
  | InitVarExists (tid : P.TypedIdent) (existing_value : P.Expr)
  | AssignVarNotExists (tid : P.Ident) (value : P.Expr)
  | HavocVarNotExists (tid : P.Ident)
  | AssertFail (label : String) (b : P.Expr)
  | AssumeFail (label : String) (b : P.Expr)
  | LabelNotExists (label : String)
  | Misc (f : Format)
  | OutOfFuel

def EvalError.toFormat [ToFormat P.Expr] [ToFormat P.Ident] [ToFormat P.Ty]
    (e : EvalError P) : Format :=
  match e with
  | .InitVarExists var val =>
    (f!"[INIT ERROR] Variable {var} already exists, with current value {val}.")
  | AssignVarNotExists var val =>
    (f!"[ASSIGN ERROR] Variable {var} has not been declared yet, so it \
       cannot be assigned to {val}.")
  | HavocVarNotExists var =>
    (f!"[HAVOC ERROR] Variable {var} has not been declared yet, so it \
       cannot be havocked.")
  | AssertFail label b =>
    (f!"[ASSERT ERROR] Assertion {label} failed!{Format.line}{b}")
  | AssumeFail label b =>
    (f!"[ASSUME ERROR] Assumption {label} falsified!{Format.line}{b}")
  | LabelNotExists label =>
    (f!"[GOTO ERROR] Label {label} does not exist later in the program.")
  | OutOfFuel =>
    (f!"[ERROR] Ran out of fuel.")
  | Misc f =>
    (f!"[ERROR] {f}")

instance [ToFormat P.Expr] [ToFormat P.Ident] [ToFormat P.Ty] : ToFormat (EvalError P) where
  format := EvalError.toFormat

---------------------------------------------------------------------

end Imperative
