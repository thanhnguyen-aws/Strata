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

import Strata.Languages.C_Simp.DDMTransform.Parse
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.Loopy
import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Identifiers

-- We define the AST for our language here.

-- The CST and grammar are defined in `DDMTransform/Parse.lean`
-- The conversion to this AST are defined in `DDMTransform/Translate.lean`
-- Typechecking is done in ___ (TODO)
-- We symbolically execute the C_Simp program in ___, collecting path conditions. (TODO)

namespace Strata
namespace C_Simp

-- Our expression language is `DL/Lambda`
abbrev Expression : Imperative.PureExpr := {
  Ident := String,
  Expr := Lambda.LExpr String,
  Ty := Lambda.LTy,
  TyEnv := Lambda.TEnv String,
  EvalEnv := Lambda.LState String,
  EqIdent := String.decEq
}

-- Our statement language is `DL/Imp` with `DL/Lambda` as the expression language
-- abbrev Statement := Loopy.LoopOrStmt
-- abbrev Command := Imperative.Cmd C_Simp.Expression

-- A program is a list of functions. We start by defining functions

structure Function where
  name: Expression.Ident
  pre : Expression.Expr
  post : Expression.Expr
  body : List Loopy.LoopOrStmt
  ret_ty : Lambda.LMonoTy
  inputs : Map Expression.Ident Lambda.LMonoTy
deriving Inhabited

structure Program where
  funcs : List Function

-- Instances

-- Provide ToFormat instances for DefaultPureExpr components
instance : Std.ToFormat Loopy.DefaultPureExpr.Ident where
  format s := Std.Format.text s  -- Convert String to Format

instance : Std.ToFormat Loopy.DefaultPureExpr.Expr where
  format e := (inferInstance : Std.ToFormat (Lambda.LExpr String)).format e

instance : Std.ToFormat Loopy.DefaultPureExpr.Ty where
  format t := (inferInstance : Std.ToFormat Lambda.LTy).format t

instance : Std.ToFormat Function where
  format f :=
    "function " ++ Std.format f.name ++ " {\n" ++
    "  pre: " ++ Std.format f.pre ++ "\n" ++
    "  post: " ++ Std.format f.post ++ "\n" ++
    "  body:\n" ++ Std.format f.body ++ "\n" ++
    "}"

instance : Std.ToFormat Program where
  format p := Std.Format.joinSep (p.funcs.map Std.format) Std.Format.line

---------------------------------------------------------------------

instance : ToString (Program) where
  toString p := toString (Std.format p)

end C_Simp
end Strata
