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

/-
Extra declarations in Fin namespace
-/

namespace Fin

instance : Min (Fin n) where
  min x y := ⟨min x.val y.val, by omega⟩

inductive Range (n : Nat) where
| mk : Range n

namespace Range

instance : ForIn m (Range n) (Fin n) where
  forIn _ b f := loop f b 0
    where loop {m} [Monad m] {β} (f : Fin n → β → m (ForInStep β)) (b : β) (i : Nat) : m β :=
            if p : i < n then do
              match ← f ⟨i, p⟩ b with
              | .done b => pure b
              | .yield b => loop f b (i+1)
            else
              pure b

end Range

def range (n : Nat) : Range n := .mk
