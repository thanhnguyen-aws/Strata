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

import Lean.Parser.Basic

namespace Lean.Parser.PrattParsingTables

def addLeadingParser (tables : PrattParsingTables) (p : Parser) (prio : Nat) : PrattParsingTables :=
  let addTokens (tks : List Token) : PrattParsingTables :=
    let tks    := tks.map Name.mkSimple
    let tables := tks.eraseDups.foldl (init := tables) fun tables tk =>
      { tables with leadingTable := tables.leadingTable.insert tk (p, prio) }
    tables
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _ => { tables with leadingParsers := (p, prio) :: tables.leadingParsers }

private def addTrailingParser (tables : PrattParsingTables) (p : TrailingParser) (prio : Nat) : PrattParsingTables :=
  let addTokens (tks : List Token) : PrattParsingTables :=
    let tks := tks.map fun tk => Name.mkSimple tk
    tks.eraseDups.foldl (init := tables) fun tables tk =>
      { tables with trailingTable := tables.trailingTable.insert tk (p, prio) }
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _                         => { tables with trailingParsers := (p, prio) :: tables.trailingParsers }

def addParser (tables : PrattParsingTables) (leading : Bool) (p : Parser) (prio : Nat) : PrattParsingTables :=
  match leading, p with
  | true, p  => addLeadingParser tables p prio
  | false, p => addTrailingParser tables p prio

end Lean.Parser.PrattParsingTables
