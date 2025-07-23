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

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

class TypeContext (P : PureExpr) (T : Type) where
  isBoolType   : P.Ty → Bool
  freeVars     : P.Expr → List P.Ident
  preprocess   : T → P.Ty → Except Format (P.Ty × T)
  postprocess  : T → P.Ty → Except Format (P.Ty × T)
  update       : T → P.Ident → P.Ty → T
  lookup       : T → P.Ident → Option P.Ty
  inferType    : T → Cmd P → P.Expr → Except Format (P.Expr × P.Ty × T)
  unifyTypes   : T → List (P.Ty × P.Ty) → Except Format T

---------------------------------------------------------------------
end Imperative
