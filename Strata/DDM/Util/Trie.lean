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

import Lean.Data.Trie

open Lean.Data (Trie)

namespace Lean.Data.Trie

private def ppElt (s : String) (lineStarted : Bool) (indent : String) (val : String) : String :=
  if lineStarted then
    s ++ " " ++ val
  else
    s ++ indent ++ val

private def ppAux [ToString α] (t : Trie α) (lineStarted : Bool) (indent : String) (s : String) : String :=
  match t with
  | .leaf none =>
    ppElt s lineStarted indent (toString ".none\n")
  | .leaf (some a) =>
    ppElt s lineStarted indent (toString a ++ "\n")
  | .node1 none v u =>
    let s := ppElt s lineStarted (indent ++ " ") (toString v)
    ppAux u true indent s
  | .node1 ma v u =>
    let (started, s) :=
          match ma with
          | some a => (false, ppElt s lineStarted indent (toString a ++ "\n"))
          | none => (lineStarted, s)
    let s := ppElt s started (indent ++ " ") (toString v)
    ppAux u true indent s
  | .node ma bytes tries =>
    if q : bytes.size = tries.size then
      let s :=
            match ma with
            | some a => ppElt s lineStarted indent (toString a ++ "\n")
            | none => ppElt s lineStarted indent (".end\n")
      let indent := indent ++ " "
      bytes.size.fold (init := s) fun i h s =>
        let b := bytes[i]
        let t := tries[i]
        let s := ppElt s false indent (toString b)
        ppAux t true indent s
    else
      panic! s!"Bad sizes {bytes.size} {tries.size}"

/--
This renders the trie so that it is a bit easier to see the structure.
-/
private def ppStructure [ToString α] (t : Trie α) : String :=
  ppAux t false "" ""
