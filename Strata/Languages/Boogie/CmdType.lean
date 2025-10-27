/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.OldExpressions
import Strata.Languages.Boogie.Expressions
import Strata.DL.Imperative.TypeContext

namespace Boogie
open Lambda Imperative
open Std (ToFormat Format format)
---------------------------------------------------------------------

namespace CmdType

def isBoolType (ty : LTy) : Bool :=
  match ty with
  | .forAll [] LMonoTy.bool => true
  | _ => false

def lookup (T : (TEnv Visibility)) (x : BoogieIdent) : Option LTy :=
  T.context.types.find? x

def update (T : TEnv Visibility) (x : BoogieIdent) (ty : LTy) : TEnv Visibility :=
  T.insertInContext x ty

def freeVars (e : (LExpr LMonoTy Visibility)) : List BoogieIdent :=
  (LExpr.freeVars e).map (fun (i, _) => i)

/--
Preprocess a user-facing type in Boogie amounts to converting a poly-type (i.e.,
`LTy`) to a mono-type (i.e., `LMonoTy`) via instantiation. We still return an
`LTy`, with no bound variables.
-/
def preprocess (T : TEnv Visibility) (ty : LTy) : Except Format (LTy × TEnv Visibility) := do
  let (mty, T) ← ty.instantiateWithCheck T
  return (.forAll [] mty, T)

def postprocess (T : TEnv Visibility) (ty : LTy) : Except Format (LTy × TEnv Visibility) := do
  if h: ty.isMonoType then
    let ty := LMonoTy.subst T.state.substInfo.subst (ty.toMonoType h)
    .ok (.forAll [] ty, T)
  else
    .error f!"[postprocess] Expected mono-type; instead got {ty}"

/--
The inferred type of `e` will be an `LMonoTy`, but we return an `LTy` with no
bound variables.
-/
def inferType (T : TEnv Visibility) (c : Cmd Expression) (e : (LExpr LMonoTy Visibility)) :
    Except Format ((LExpr LMonoTy Visibility) × LTy × TEnv Visibility) := do
  -- We only allow free variables to appear in `init` statements. Any other
  -- occurrence leads to an error.
  let T ← match c with
    | .init _ _ _ _ =>
      let efv := LExpr.freeVars e
      .ok (T.addInOldestContext efv)
    | _ =>
      let _ ← T.freeVarCheck e f!"[{c}]"
      .ok T
  let e := OldExpressions.normalizeOldExpr e
  let (ea, T) ← LExprT.fromLExpr T e
  let ety := ea.toLMonoTy
  return (ea.toLExpr, (.forAll [] ety), T)

/--
Type constraints come from functions `inferType` and `preprocess`, both of which
are expected to return `LTy`s with no bound variables which can be safely
converted to `LMonoTy`s.
-/
def canonicalizeConstraints (constraints : List (LTy × LTy)) : Except Format Constraints := do
  match constraints with
  | [] => .ok []
  | (t1, t2) :: c_rest =>
    if h: t1.isMonoType && t2.isMonoType then
      let t1 := t1.toMonoType (by simp_all)
      let t2 := t2.toMonoType (by simp at h; simp_all only)
      let c_rest ← canonicalizeConstraints c_rest
      .ok ((t1, t2) :: c_rest)
    else
      .error f!"[canonicalizeConstraints] Expected to see only mono-types in \
                type constraints, but found the following instead:\n\
                t1: {t1}\nt2: {t2}\n"

def unifyTypes (T : TEnv Visibility) (constraints : List (LTy × LTy)) : Except Format (TEnv Visibility) := do
  let constraints ← canonicalizeConstraints constraints
  let S ← Constraints.unify constraints T.state.substInfo
  let T := T.updateSubst S
  return T

---------------------------------------------------------------------

instance : Imperative.TypeContext Expression (TEnv Visibility) where
  isBoolType  := CmdType.isBoolType
  freeVars    := CmdType.freeVars
  preprocess  := CmdType.preprocess
  postprocess := CmdType.postprocess
  update      := CmdType.update
  lookup      := CmdType.lookup
  inferType   := CmdType.inferType
  unifyTypes  := CmdType.unifyTypes

end CmdType
---------------------------------------------------------------------

end Boogie
