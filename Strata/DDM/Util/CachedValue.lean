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

import Lean.ToExpr

structure CachedValue {α} (v : α) where
  val : α := v
  isEqual : val = v := by trivial

namespace CachedValue

protected def default {α : Sort u} (v : α) : CachedValue v := {}

instance {α} (v : α) : Inhabited (CachedValue v) where
  default := .default v

instance  {α : Type _} (v : α) : Repr (CachedValue v) where
  reprPrec _ _ := .text "{}"

instance {α} (v : α) : CoeOut (CachedValue v) α where
  coe s := s.val

open Lean

instance {α : Type} [h : Lean.ToExpr α] (v : α) : Lean.ToExpr (CachedValue v) where
  toTypeExpr := mkApp2 (mkConst ``CachedValue [levelOne]) h.toTypeExpr (toExpr v)
  toExpr _ := mkApp2 (mkConst ``CachedValue.default [levelOne]) h.toTypeExpr (toExpr v)

instance {α : Type} [h : Quote α] (v : α) : Quote (CachedValue v) where
  quote _ := Syntax.mkCApp ``CachedValue.default #[quote v]

end CachedValue
