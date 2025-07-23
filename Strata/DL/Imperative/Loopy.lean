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

import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LState
import Strata.DL.Imperative.Cmd


/-
The idea is to add `while` loops as a language construct, but to keep them separate from the other Statements.
We won't support loops in Symbolic Execution; but we'll provide a pass to eliminate the loops.

A loop must have a measure (to ensure termination) and an invariant.





A loop is replaced with the following:




-/

namespace Strata

namespace Loopy

open Imperative

-- TODO: for the transformation, we need to know P.Expr
-- so we can write our transformation
def DefaultPureExpr : PureExpr := {
  Ident := String,
  Expr := Lambda.LExpr String,
  Ty := Lambda.LTy,
  TyEnv := Lambda.TEnv String,
  EvalEnv := Lambda.LState String,
  EqIdent := String.decEq
}

def Command := Imperative.Cmd DefaultPureExpr

instance : HasVarsImp DefaultPureExpr Command where
  definedVars := Cmd.definedVars
  modifiedVars := Cmd.modifiedVars

inductive LoopOrStmt : Type where
  | loop (guard: DefaultPureExpr.Expr) (body: Block DefaultPureExpr Command) (measure: Option DefaultPureExpr.Expr) (invariant: Option DefaultPureExpr.Expr)
  | stmt (s : Stmt DefaultPureExpr Command)
deriving Inhabited

def LoopOrStmt.definedVars (lors : LoopOrStmt) : List DefaultPureExpr.Ident :=
  match lors with
  | .loop _ body _ _ => Stmts.definedVars body.ss
  | .stmt s => Stmt.definedVars s

def LoopOrStmt.modifiedVars (lors : LoopOrStmt) : List DefaultPureExpr.Ident :=
  match lors with
  | .loop _ body _ _ => Stmts.definedVars body.ss
  | .stmt s => Stmt.definedVars s

instance : HasVarsImp DefaultPureExpr LoopOrStmt where
  definedVars := LoopOrStmt.definedVars
  modifiedVars := LoopOrStmt.modifiedVars

abbrev LoopOrStmts := List LoopOrStmt

def LoopOrStmts.definedVars (l : LoopOrStmts) : List DefaultPureExpr.Ident :=
  (l.map (λ lors => lors.definedVars)).flatten

def LoopOrStmts.modifiedVars (l : LoopOrStmts) : List DefaultPureExpr.Ident :=
  (l.map (λ lors => lors.modifiedVars)).flatten

-- instance : HasVarsImp DefaultPureExpr (List LoopOrStmt) where
--   definedVars l :=
--   modifiedVars l :=


---------------------------------------------------------------------

/-! ## Formatting -/

open Std (ToFormat Format format)


def formatLoopOrStmt (s : LoopOrStmt)
 [ToFormat DefaultPureExpr.Ident] [ToFormat DefaultPureExpr.Expr] [ToFormat DefaultPureExpr.Ty] [ToFormat Command] : Format :=
  match s with
  | .stmt s => formatStmt DefaultPureExpr s
  | .loop g b m i => f!"while({g})\n" ++
                     f!"({m})\n" ++
                     f!"({i})\n" ++
                 Format.bracket "{" f!"{formatStmts DefaultPureExpr b.ss}" "}" ++
                 ""

def formatLoopOrStmts (ss : List LoopOrStmt)
 [ToFormat DefaultPureExpr.Ident] [ToFormat DefaultPureExpr.Expr] [ToFormat DefaultPureExpr.Ty] [ToFormat Command] : Format :=
  match ss with
  | [] => f!""
  | h :: t =>
    formatLoopOrStmt h ++
    if t.isEmpty then f!""
    else f!"\n{formatLoopOrStmts t}"

instance [ToFormat DefaultPureExpr.Ident] [ToFormat DefaultPureExpr.Expr] [ToFormat DefaultPureExpr.Ty] : ToFormat Command where
  format c := Imperative.formatCmd DefaultPureExpr c

instance [ToFormat DefaultPureExpr.Ident] [ToFormat DefaultPureExpr.Expr] [ToFormat DefaultPureExpr.Ty] [ToFormat Command]:
  ToFormat (LoopOrStmt) where
  format s := formatLoopOrStmt s

instance [ToFormat DefaultPureExpr.Ident] [ToFormat DefaultPureExpr.Expr] [ToFormat DefaultPureExpr.Ty] [ToFormat Command]:
  ToFormat (List LoopOrStmt) where
  format ss := formatLoopOrStmts ss

---------------------------------------------------------------------

end Loopy
end Strata
