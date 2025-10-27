/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF

/-! ## Type Inference Transform for Lambda Expressions.

Type inference that transforms `LExpr` to annotated `LExprT`. `LExprT` is very
similar to `LExpr`, except that we mandate every constructor's annotation with
an inferred (mono)type.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open LTy

variable {IDMeta : Type} [DecidableEq IDMeta] [HasGen IDMeta]

/--
Apply type substitution `S` to `LExpr e`.
-/
def LExpr.applySubst (e : (LExpr LMonoTy IDMeta)) (S : Subst) : (LExpr LMonoTy IDMeta) :=
  match e with
  | .const c ty =>
    match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .const c ty
  | .op o ty =>
    match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .op o ty
  | .fvar x ty =>
      match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .fvar x ty
  | .bvar _ => e
  | .abs ty e => .abs ty (e.applySubst S)
  | .quant qk ty tr e => .quant qk ty (tr.applySubst S) (e.applySubst S)
  | .app e1 e2 => .app (e1.applySubst S) (e2.applySubst S)
  | .ite c t f => .ite (c.applySubst S) (t.applySubst S) (f.applySubst S)
  | .eq e1 e2 => .eq (e1.applySubst S) (e2.applySubst S)
  | .mdata m e => .mdata m (e.applySubst S)

/--
Monotype-annotated Lambda expressions, obtained after a type inference transform
from Lambda expressions `LExpr`.
-/
inductive LExprT (IDMeta : Type): Type where
  | const (c : String) (ty : LMonoTy)
  | op    (c : Identifier IDMeta) (ty : LMonoTy)
  | bvar (deBruijnIndex : Nat) (ty : LMonoTy)
  | fvar (name : Identifier IDMeta) (ty : LMonoTy)
  | mdata (info : Info) (e : LExprT IDMeta)
  | abs (e : LExprT IDMeta) (ty : LMonoTy)
  | quant (k : QuantifierKind) (argTy : LMonoTy) (triggers : LExprT IDMeta) (e : LExprT IDMeta)
  | app (fn e : LExprT IDMeta) (ty : LMonoTy)
  | ite (c t e : LExprT IDMeta) (ty : LMonoTy)
  | eq (e1 e2 : LExprT IDMeta) (ty : LMonoTy)
  deriving Repr, DecidableEq

partial def LExprT.format (et : (LExprT IDMeta)) : Std.Format :=
  match et with
  | .const c ty => f!"(#{c} : {ty})"
  | .op o ty => f!"(~{o} : {ty})"
  | .bvar i ty => f!"(%{i} : {ty})"
  | .fvar x ty => f!"({x} : {ty})"
  | .mdata m e => f!"(.mdata {repr m} {LExprT.format e})"
  | .abs e ty => f!"((λ {LExprT.format e}) : {ty})"
  | .quant .all ty _ e => f!"(∀({ty}) {LExprT.format e})"
  | .quant .exist ty _ e => f!"(∃({ty}) {LExprT.format e})"
  | .app e1 e2 ty => f!"({LExprT.format e1} {LExprT.format e2}) : {ty})"
  | .ite c t f ty => f!"(if {LExprT.format c} then \
                            {LExprT.format t} else \
                            {LExprT.format f}) : {ty})"
  | .eq e1 e2 ty => f!"({LExprT.format e1} == {LExprT.format e2}) : {ty})"

instance : ToFormat (LExprT IDMeta) where
  format := LExprT.format

---------------------------------------------------------------------

namespace LExprT

/--
Obtain the monotype from `LExprT e`.
-/
def toLMonoTy (e : (LExprT IDMeta)) : LMonoTy :=
  match e with
  | .const _ ty | .op _ ty | .bvar _ ty | .fvar _ ty
  | .app _ _ ty | .abs _ ty | .ite _ _ _ ty | .eq _ _ ty => ty
  | .quant _ _ _ _ => LMonoTy.bool
  | .mdata _ et => LExprT.toLMonoTy et

/--
Obtain an `LExpr` from an `LExprT`. We erase type annotations for all
expressions, except the constants `.const`s, `.op`s, and free variables
`.fvar`s.
-/
def toLExpr (e : (LExprT IDMeta)) : (LExpr LMonoTy IDMeta) :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op o ty
  | .bvar b _ => .bvar b
  | .fvar f ty => .fvar f ty
  | .app e1 e2 _ =>
    .app e1.toLExpr e2.toLExpr
  | .abs e (.arrow aty _) => .abs aty e.toLExpr
  | .abs e _ => .abs .none e.toLExpr
  | .quant qk ty tr e => .quant qk ty tr.toLExpr e.toLExpr
  | .ite c t f _ => .ite c.toLExpr t.toLExpr f.toLExpr
  | .eq e1 e2 _ => .eq e1.toLExpr e2.toLExpr
  | .mdata m e => .mdata m e.toLExpr

/--
Apply type substitution `S` to `LExprT e`.
-/
def applySubst (e : (LExprT IDMeta)) (S : Subst) : (LExprT IDMeta) :=
  match e with
  | .const c ty =>
    let ty := LMonoTy.subst S ty
    .const c ty
  | .op o ty =>
    let ty := LMonoTy.subst S ty
    .op o ty
  | .bvar b ty =>
    let ty := LMonoTy.subst S ty
    .bvar b ty
  | .fvar x ty =>
    let ty := LMonoTy.subst S ty
    .fvar x ty
  | .app e1 e2 ty =>
    let e1 := LExprT.applySubst e1 S
    let e2 := LExprT.applySubst e2 S
    let ty := LMonoTy.subst S ty
    .app e1 e2 ty
  | .abs e ty =>
    let e := LExprT.applySubst e S
    let ty := LMonoTy.subst S ty
    .abs e ty
  | .quant qk ty tr e =>
    let e := LExprT.applySubst e S
    let tr := LExprT.applySubst tr S
    .quant qk ty tr e
  | .ite c t f ty =>
    let c := LExprT.applySubst c S
    let t := LExprT.applySubst t S
    let f := LExprT.applySubst f S
    let ty := LMonoTy.subst S ty
    .ite c t f ty
  | .eq e1 e2 ty =>
    let e1 := LExprT.applySubst e1 S
    let e2 := LExprT.applySubst e2 S
    let ty := LMonoTy.subst S ty
    .eq e1 e2 ty
  | .mdata m e =>
    let e := LExprT.applySubst e S
    .mdata m e

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)` in an `LExprT e`.

Also see `LExpr.varClose` for an analogous function for `LExpr`s.
-/
protected def varClose (k : Nat) (x : Identifier IDMeta) (e : (LExprT IDMeta)) : (LExprT IDMeta) :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op o ty
  | .bvar i ty => .bvar i ty
  | .fvar y yty => if (x == y) then (.bvar k yty)
                               else (.fvar y yty)
  | .mdata info e' => .mdata info (.varClose k x e')
  | .abs e' ty => .abs (.varClose (k + 1) x e') ty
  | .quant qk ty tr' e' => .quant qk ty (.varClose (k + 1) x tr') (.varClose (k + 1) x e')
  | .app e1 e2 ty => .app (.varClose k x e1) (.varClose k x e2) ty
  | .ite c t e ty => .ite (.varClose k x c) (.varClose k x t) (.varClose k x e) ty
  | .eq e1 e2 ty => .eq (.varClose k x e1) (.varClose k x e2) ty

---------------------------------------------------------------------

/--
Generate a fresh identifier `xv` for a bound variable. Use the type annotation
`ty` if present, otherwise generate a fresh type variable. Add `xv` along with
its type to the type context.
-/
def typeBoundVar (T : TEnv IDMeta) (ty : Option LMonoTy) :
  Except Format (Identifier IDMeta × LMonoTy × TEnv IDMeta) := do
  let (xv, T) := HasGen.genVar T
  let (xty, T) ← match ty with
    | some bty =>
      let ans := LMonoTy.instantiateWithCheck bty T
      match ans with
      | .error e => .error e
      | .ok (bty, T) => .ok (bty, T)
    | none =>
      let (xtyid, T) := TEnv.genTyVar T
      let xty := (LMonoTy.ftvar xtyid)
      .ok (xty, T)
  let T := T.insertInContext xv (.forAll [] xty)
  return (xv, xty, T)

/-- Infer the type of `.fvar x fty`. -/
def inferFVar (T : (TEnv IDMeta)) (x : Identifier IDMeta) (fty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv IDMeta)) :=
  match T.context.types.find? x with
  | none => .error f!"Cannot find this fvar in the context! \
                      {LExpr.fvar x fty}"
  | some ty => do
    let (ty, T) ← LTy.instantiateWithCheck ty T
    match fty with
    | none => .ok (ty, T)
    | some fty =>
      let (fty, T) ← LMonoTy.instantiateWithCheck fty T
      let S ← Constraints.unify [(fty, ty)] T.state.substInfo
      .ok (ty, TEnv.updateSubst T S)

/--
Infer the type of `.const c cty`. Here, we use the term "constant" in the same
sense as "literal".

For now, we have built-in support for booleans, integers, and strings. Note that
`LExpr` is extensible in the sense that support for new constants can be added
in the `Factory`, where a 0-ary function could be used to stand in for a
constant. However, pragmatically, we may want to incorporate first-class support
for some kinds of constants, especially for types with really large or infinite
members (e.g., bitvectors, natural numbers, etc.). `.const` is the place to do
that.
-/
def inferConst (T : (TEnv IDMeta)) (c : String) (cty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv IDMeta)) :=
  open LTy.Syntax in
  match c, cty with
  -- Annotated Booleans
  | "true", some LMonoTy.bool | "false", some LMonoTy.bool => .ok (mty[bool], T)
  -- Unannotated Booleans: note that `(.const "true" none)` and
  -- `(.const "false" none)` will be interpreted as booleans.
  | "true", none | "false", none =>
    if { name := "bool" } ∈ T.knownTypes then
      .ok (mty[bool], T)
    else
      .error f!"Booleans are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const LMonoTy IDMeta c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated Integers
  | c, some LMonoTy.int =>
    if { name := "int" } ∈ T.knownTypes then
      if c.isInt then .ok (mty[int], T)
                 else .error f!"Constant annotated as an integer, but it is not.\n\
                                {@LExpr.const LMonoTy IDMeta c cty}"
    else
      .error f!"Integers are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const LMonoTy IDMeta c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated Reals
  | c, some LMonoTy.real =>
    if { name := "real" } ∈ T.knownTypes then
      .ok (mty[real], T)
    else
      .error f!"Reals are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const LMonoTy IDMeta c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated BitVecs
  | c, some (LMonoTy.bitvec n) =>
    let ty := LMonoTy.bitvec n
    if { name := "bitvec", arity := 1 } ∈ T.knownTypes then
      (.ok (ty, T))
    else
      .error f!"Bit vectors of size {n} are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const LMonoTy IDMeta c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated Strings
  | c, some LMonoTy.string =>
    if { name := "string" } ∈ T.knownTypes then
      .ok (mty[string], T)
    else
      .error f!"Strings are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const LMonoTy IDMeta c cty}\n\
                Known Types: {T.knownTypes}"
  | _, _ =>
  -- Unannotated Integers
    if c.isInt then
      if { name := "int" } ∈ T.knownTypes then
        .ok (mty[int], T)
      else
        .error f!"Integers are not registered in the known types.\n\
                  Constant {@LExpr.const LMonoTy IDMeta c cty}\n\
                  Known Types: {T.knownTypes}"
    else
      .error f!"Cannot infer the type of this constant: \
                {@LExpr.const LMonoTy IDMeta c cty}"

mutual
partial def fromLExprAux (T : (TEnv IDMeta)) (e : (LExpr LMonoTy IDMeta)) :
    Except Format ((LExprT IDMeta) × (TEnv IDMeta)) :=
  open LTy.Syntax in do
  match e with
  | .mdata m e =>
    let (et, T) ← fromLExprAux T e
    .ok ((.mdata m et), T)
  | .const c cty =>
    let (ty, T) ← inferConst T c cty
    .ok (.const c ty, T)
  | .op o oty =>
    let (ty, T) ← inferOp T o oty
    .ok (.op o ty, T)
  | .bvar _ => .error f!"Cannot infer the type of this bvar: {e}"
  | .fvar x fty =>
    let (ty, T) ← inferFVar T x fty
    .ok (.fvar x ty, T)
  | .app e1 e2   => fromLExprAux.app T e1 e2
  | .abs ty e    => fromLExprAux.abs T ty e
  | .quant qk ty tr e => fromLExprAux.quant T qk ty tr e
  | .eq e1 e2    => fromLExprAux.eq T e1 e2
  | .ite c th el => fromLExprAux.ite T c th el

/-- Infer the type of an operation `.op o oty`, where an operation is defined in
  the factory. -/
partial def inferOp (T : (TEnv IDMeta)) (o : Identifier IDMeta) (oty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv IDMeta)) :=
  open LTy.Syntax in
  match T.functions.find? (fun fn => fn.name == o) with
  | none =>
    .error f!"{toString $ T.functions.getFunctionNames} Cannot infer the type of this operation: \
              {LExpr.op o oty}"
  | some func => do
      -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
      -- where there are duplicates in the formals, etc.).
      let type ← func.type
      let (ty, T) ← LTy.instantiateWithCheck type T
      let T ←
        match func.body with
        | none => .ok T
        | some body =>
          if body.freeVars.idents.all (fun k => k ∈ func.inputs.keys) then
            -- Temporarily add formals in the context.
            let T := T.pushEmptyContext
            let T := T.addToContext func.inputPolyTypes
            -- Type check the body and ensure that it unifies with the return type.
            -- let (bodyty, T) ← infer T body
            let (body_typed, T) ← fromLExprAux T body
            let bodyty := body_typed.toLMonoTy
            let (retty, T) ← func.outputPolyType.instantiateWithCheck T
            let S ← Constraints.unify [(retty, bodyty)] T.state.substInfo
            let T := T.updateSubst S
            let T := T.popContext
            .ok T
          else
            .error f!"Function body contains free variables!\n\
                      {func}"
      match oty with
      | none => .ok (ty, T)
      | some oty =>
        let (oty, T) ← LMonoTy.instantiateWithCheck oty T
        let S ← Constraints.unify [(ty, oty)] T.state.substInfo
        .ok (ty, TEnv.updateSubst T S)

partial def fromLExprAux.ite (T : (TEnv IDMeta)) (c th el : (LExpr LMonoTy IDMeta)) := do
  let (ct, T) ← fromLExprAux T c
  let (tt, T) ← fromLExprAux T th
  let (et, T) ← fromLExprAux T el
  let cty := ct.toLMonoTy
  let tty := tt.toLMonoTy
  let ety := et.toLMonoTy
  let S ← Constraints.unify [(cty, LMonoTy.bool), (tty, ety)] T.state.substInfo
  .ok (.ite ct tt et tty, TEnv.updateSubst T S)

partial def fromLExprAux.eq (T : (TEnv IDMeta)) (e1 e2 : (LExpr LMonoTy IDMeta)) := do
  -- `.eq A B` is well-typed if there is some instantiation of
  -- type parameters in `A` and `B` that makes them have the same type.
  let (e1t, T) ← fromLExprAux T e1
  let (e2t, T) ← fromLExprAux T e2
  let ty1 := e1t.toLMonoTy
  let ty2 := e2t.toLMonoTy
  let S ← Constraints.unify [(ty1, ty2)] T.state.substInfo
  .ok (.eq e1t e2t LMonoTy.bool, TEnv.updateSubst T S)

partial def fromLExprAux.abs (T : (TEnv IDMeta)) (bty : Option LMonoTy) (e : (LExpr LMonoTy IDMeta)) := do
  -- Generate a fresh expression variable to stand in for the bound variable.
  -- For the bound variable, use type annotation if present. Otherwise,
  -- generate a fresh type variable.
  let (xv, xty, T) ← typeBoundVar T bty
  -- Construct `e'` from `e`, where the bound variable has been replaced by
  -- `xv`.
  let e' := LExpr.varOpen 0 (xv, some xty) e
  let (et, T) ← fromLExprAux T e'
  let etclosed := .varClose 0 xv et
  let ety := etclosed.toLMonoTy
  let mty := LMonoTy.subst T.state.substInfo.subst (.tcons "arrow" [xty, ety])
  -- Safe to erase fresh variable from context after closing the expressions.
  -- Note that we don't erase `xty` (if it was a fresh type variable) from the substitution
  -- list because it may occur in `etclosed`, which hasn't undergone a
  -- substitution. We could, of course, substitute `xty` in `etclosed`, but
  -- that'd require crawling over that expression, which could be expensive.
  let T := T.eraseFromContext xv
  .ok ((.abs etclosed mty), T)

partial def fromLExprAux.quant (T : (TEnv IDMeta)) (qk : QuantifierKind) (bty : Option LMonoTy)
    (triggers : LExpr LMonoTy IDMeta) (e : (LExpr LMonoTy IDMeta)) := do
  let (xv, xty, T) ← typeBoundVar T bty
  let e' := LExpr.varOpen 0 (xv, some xty) e
  let triggers' := LExpr.varOpen 0 (xv, some xty) triggers
  let (et, T) ← fromLExprAux T e'
  let (triggersT, T) ← fromLExprAux T triggers'
  let ety := et.toLMonoTy
  let xty := LMonoTy.subst T.state.substInfo.subst xty
  let etclosed := LExprT.varClose 0 xv et
  let triggersClosed := LExprT.varClose 0 xv triggersT
  -- Safe to erase fresh variable from context after closing the expressions.
  -- Again, as in `abs`, we do not erase `xty` (if it was a fresh variable) from the
  -- substitution list.
  let T := T.eraseFromContext xv
  if ety != LMonoTy.bool then do
    .error f!"Quantifier body has non-Boolean type: {ety}"
  else
    .ok (.quant qk xty triggersClosed etclosed, T)

partial def fromLExprAux.app (T : (TEnv IDMeta)) (e1 e2 : (LExpr LMonoTy IDMeta)) := do
  let (e1t, T) ← fromLExprAux T e1
  let ty1 := e1t.toLMonoTy
  let (e2t, T) ← fromLExprAux T e2
  let ty2 := e2t.toLMonoTy
  -- `freshty` is the type variable whose identifier is `fresh_name`. It denotes
  -- the type of `(.app e1 e2)`.
  let (fresh_name, T) := TEnv.genTyVar T
  let freshty := (.ftvar fresh_name)
  -- `ty1` must be of the form `ty2 → freshty`.
  let constraints := [(ty1, (.tcons "arrow" [ty2, freshty]))]
  let S ← Constraints.unify constraints T.state.substInfo
  -- The type of `(.app e1 e2)` is `freshty`, with appropriate substitutions
  -- applied.
  let mty := LMonoTy.subst S.subst freshty
  -- `freshty` can now be safely removed from the substitution list.
  have hWF : SubstWF (Maps.remove S.subst fresh_name) := by
    apply @SubstWF_of_remove S.subst fresh_name S.isWF
  let S := { S with subst := S.subst.remove fresh_name, isWF := hWF }
  .ok (.app e1t e2t mty, TEnv.updateSubst T S)

end

protected def fromLExpr (T : (TEnv IDMeta)) (e : (LExpr LMonoTy IDMeta)) :
    Except Format ((LExprT IDMeta) × (TEnv IDMeta)) := do
  let (et, T) ← fromLExprAux T e
  .ok (LExprT.applySubst et T.state.substInfo.subst, T)

protected def fromLExprs (T : (TEnv IDMeta)) (es : List (LExpr LMonoTy IDMeta)) :
    Except Format (List (LExprT IDMeta) × (TEnv IDMeta)) := do
  go T es []
  where
    go (T : TEnv IDMeta) (rest : List (LExpr LMonoTy IDMeta))
        (acc : List (LExprT IDMeta)) := do
      match rest with
      | [] => .ok (acc.reverse, T)
      | e :: erest =>
        let (et, T) ← LExprT.fromLExpr T e
        go T erest (et :: acc)

end LExprT

---------------------------------------------------------------------

/--
Annotate an `LExpr e` with inferred monotypes.
-/
def LExpr.annotate (T : (TEnv IDMeta)) (e : (LExpr LMonoTy IDMeta)) :
    Except Format ((LExpr LMonoTy IDMeta) × (TEnv IDMeta)) := do
  let (e_a, T) ← LExprT.fromLExpr T e
  return (LExprT.toLExpr e_a, T)

---------------------------------------------------------------------

end Lambda
