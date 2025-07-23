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
Functions for ByteArray that could potentially be upstreamed to Lean.
-/
namespace ByteArray

deriving instance DecidableEq for ByteArray

def back! (a : ByteArray) : UInt8 := a.get! (a.size - 1)

def back? (a : ByteArray) : Option UInt8 := a[a.size - 1]?

def pop (a : ByteArray) : ByteArray := a.extract 0 (a.size - 1)

@[inline]
def foldr {β} (f : UInt8 → β → β) (init : β) (as : ByteArray) (start := as.size) (stop := 0) : β :=
  let rec aux (i : Nat) (p : i ≤ as.size) (b : β) :=
      if h : i ≤ stop then
        b
      else
        have q : i - i < as.size := by omega
        aux (i-1) (by omega) (f as[i-1] b)
  aux (min start as.size) (Nat.min_le_right _ _) init

def asHex (a : ByteArray) : String :=
  a.foldl (init := "") fun s b =>
    let cl := Nat.toDigits 16 b.toNat
    let cl := if cl.length < 2 then '0' :: cl else cl
    s ++ cl.asString

end ByteArray

#guard (ByteArray.empty |>.back!) = default
#guard (ByteArray.empty |>.push 4 |>.back!) = 4

#guard (ByteArray.empty |>.pop) = .empty
#guard let a := ByteArray.empty |>.push 0 |>.push 1; (a |>.push 2 |>.pop) = a
