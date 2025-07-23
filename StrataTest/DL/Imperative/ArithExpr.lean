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

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.EvalError
import Strata.DL.Util.Maps

namespace Arith
open Std (ToFormat Format format)
open Imperative

---------------------------------------------------------------------

inductive Ty where
  | Num | Bool
  deriving DecidableEq, Repr, Inhabited

instance : ToFormat Ty where
  format t := match t with | .Num => "Num" | .Bool => ".Bool"

/--
A type environment maps variable names to types.
-/
abbrev TEnv := Map String Ty

def TEnv.init : TEnv := []

instance : ToFormat TEnv where
  format := Map.format'

/--
Simple arithmetic expressions that will be used to specialize Imperative's
partial evaluator.
-/
inductive Expr where
  | Plus (e1 e2 : Expr)
  | Mul (e1 e2 : Expr)
  | Eq (e1 e2 : Expr)
  | Num (n : Nat)
  | Var (v : String) (ty : Option Ty)
  deriving Inhabited, Repr

def Expr.format (e : Expr) : Format :=
  match e with
  | .Plus e1 e2 => f!"{Expr.format e1} + {Expr.format e2}"
  | .Mul e1 e2 => f!"{Expr.format e1} × {Expr.format e2}"
  | .Eq e1 e2 => f!"{Expr.format e1} = {Expr.format e2}"
  | .Var v (.some ty) => f!"({v} : {ty})"
  | .Var v .none => f!"{v}"
  | .Num n => f!"{n}"

instance : ToFormat Expr where
  format := Expr.format

def Expr.freeVars (e : Expr) : List (String × Option Ty) :=
  match e with
  | .Plus e1 e2 => e1.freeVars ++ e2.freeVars
  | .Mul e1 e2 => e1.freeVars ++ e2.freeVars
  | .Eq e1 e2 => e1.freeVars ++ e2.freeVars
  | .Num _ => []
  | .Var v ty => [(v, ty)]

/--
An environment maps variable names to their types and corresponding
values (expressions).
-/
abbrev Env := Map String (Ty × Expr)

instance : ToFormat Env where
  format := Map.format'

abbrev PureExpr : PureExpr :=
   { Ident := String,
     Expr := Expr,
     Ty := Ty,
     TyEnv := TEnv,
     EvalEnv := Env,
     EqIdent := instDecidableEqString }

/-
-- Here is an alternate formulation for untyped Arith expressions.
/--
We will ignore types for this test; as such, `Expr` will be treated as untyped.
-/
inductive Untyped where
  | All
  deriving Repr

instance : ToFormat Untyped where
  format _ := f!".All"

abbrev PureExpr : PureExpr :=
   { Ident := String,
     Expr := Expr,
     Ty := Untyped,
     TyEnv := Empty,
     EvalEnv :=  Env }
-/

---------------------------------------------------------------------

end Arith
