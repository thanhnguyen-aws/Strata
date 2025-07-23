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



import Strata.DL.Lambda.LTy
import Strata.DL.Util.Map

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

section Identifiers

/--
Identifiers, optionally with their inferred monotype.
-/
abbrev IdentT (Identifier : Type) := Identifier × Option LMonoTy
abbrev IdentTs (Identifier : Type) := Map Identifier (Option LMonoTy)

instance {Identifier : Type} [ToFormat Identifier] : ToFormat (IdentT Identifier) where
  format i := match i.snd with
    | none => f!"{i.fst}"
    | some ty => f!"({i.fst} : {ty})"

def IdentT.ident (x : (IdentT Identifier)) : Identifier :=
  x.fst

def IdentT.monoty? (x : (IdentT Identifier)) : Option LMonoTy :=
  x.snd

def IdentTs.idents (xs : (IdentTs Identifier)) : List Identifier :=
  xs.keys

def IdentTs.monotys? (xs : (IdentTs Identifier)) : List (Option LMonoTy) :=
  xs.values

---------------------------------------------------------------------

end Identifiers
end Lambda
