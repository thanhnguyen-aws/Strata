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

namespace Vector

@[inline]
def modify! (v : Vector α n) (i : Nat) (f : α → α) : Vector α n where
  toArray := v.toArray.modify i f
  size_toArray := Eq.trans Array.size_modify v.size_toArray

@[inline]
def modify (v : Vector α n) (i : Fin n) (f : α → α) : Vector α n := v.modify! i.val f

end Vector
