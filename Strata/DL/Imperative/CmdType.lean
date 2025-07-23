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
import Strata.DL.Imperative.TypeContext

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

/--
Type checker for an Imperative Command.
-/
def Cmd.typeCheck [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [DecidableEq P.Ident] [TC : TypeContext P T]
    (τ : T) (c : Cmd P) : Except Format (Cmd P × T) := do

  match c with

  | .init x xty e md =>
    match TC.lookup τ x with
    | none =>
      if x ∈ TC.freeVars e then
        .error f!"Type Checking [{c}]: \
                  Variable {x} cannot appear in its own initialization expression!"
      else
        let (xty, τ) ← TC.preprocess τ xty
        let (e, ety, τ) ← TC.inferType τ c e
        let τ ← TC.unifyTypes τ [(xty, ety)]
        let (xty, τ) ← TC.postprocess τ xty
        let τ := TC.update τ x xty
        let c := Cmd.init x xty e md
        .ok (c, τ)
    | some xty =>
      .error f!"Type Checking [{c}]: Variable {x} of type {xty} already in context."

  | .set x e md =>
    match TC.lookup τ x with
    | none => .error f!"Type Checking [{c}]: Cannot set undefined variable {x}."
    | some xty =>
      let (e, ety, τ) ← TC.inferType τ c e
      let τ ← TC.unifyTypes τ [(xty, ety)]
      let c := Cmd.set x e md
      .ok (c, τ)

  | .havoc x _md =>
    match TC.lookup τ x with
    | some _ => .ok (c, τ)
    | none => .error f!"Type Checking [{c}]: Cannot havoc undefined variable {x}."

  | .assert label e md =>
    let (e, ety, τ) ← TC.inferType τ c e
    if TC.isBoolType ety then
       let c := Cmd.assert label e md
       .ok (c, τ)
    else
      .error f!"Type Checking [assert {label}]: \
                Assertion expected to be of type boolean, but inferred type is {ety}."

  | .assume label e md =>
    let (e, ety, τ) ← TC.inferType τ c e
    if TC.isBoolType ety then
       let c := Cmd.assume label e md
       .ok (c, τ)
    else
      .error f!"Type Checking [assume {label}]: \
                Assumption expected to be of type boolean, but inferred type is {ety}."

/--
Type checker for Imperative's Commands.
-/
def Cmds.typeCheck {P T} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [DecidableEq P.Ident] [TC : TypeContext P T]
    (τ : T) (cs : Cmds P) : Except Format (Cmds P × T) := do
  match cs with
  | [] => .ok ([], τ)
  | c :: crest =>
    let (c, τ) ← Cmd.typeCheck τ c
    let (crest, τ) ← Cmds.typeCheck τ crest
    .ok (c :: crest, τ)

---------------------------------------------------------------------
end Imperative
