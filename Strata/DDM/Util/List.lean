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

namespace List

theorem sizeOf_pos {α} [SizeOf α] (l : List α) : sizeOf l > 0 := by
  match l with
  | [] => simp
  | h :: l => decreasing_tactic

@[simp]
theorem sizeOf_append {α} [SizeOf α] (k l : List α) :
  sizeOf (k ++ l) = sizeOf k + sizeOf l - 1 := by
  induction k
  case nil =>
    simp
  case cons h k ind =>
    have p := sizeOf_pos l
    decreasing_tactic

/-
This is similiar to `Array.sizeOf_lt_of_mem`, but stren
-/
theorem sizeOf_lt_of_mem_strict {α} [inst : SizeOf α] {as : List α} {a} (h : a ∈ as) : sizeOf a + 2 ≤ sizeOf as := by
  induction h with
  | head as =>
    have p := sizeOf_pos as
    decreasing_tactic
  | tail _ _ ih => exact Nat.lt_trans ih (by simp +arith)

@[simp]
theorem sizeOf_set [h : SizeOf α] (as : List α) (i : Nat) (v : α)  :
    sizeOf (as.set i v) =
      if p : i < as.length then
        sizeOf as + sizeOf v - sizeOf as[i]
      else
        sizeOf as := by
  unfold List.set
  split
  case h_1 =>
    rename_i head as
    decreasing_tactic
  case h_2 =>
    rename_i b bs j
    simp [sizeOf_set _ j]
    split
    case isTrue jLt =>
      have h : sizeOf bs[j] < sizeOf bs := List.sizeOf_get _ _
      decreasing_tactic
    case isFalse jGe =>
      decreasing_tactic
  case h_3 =>
    simp

end List
