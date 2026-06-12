import Mathlib.Logic.Relation

open Lean Elab Command

theorem findIdx_go_succ {α : Type} {p : α -> Bool} {xs : List α} {i : Nat}
  : List.findIdx?.go p xs (i + 1) =
      (List.findIdx?.go p xs i).map fun n => n + 1 :=
by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : p x
      · simp [List.findIdx?.go, h]
      · simpa [List.findIdx?.go, h, Nat.add_assoc] using ih (i := i + 1)

def identStringTerm (x : Lean.TSyntax `ident) : Lean.TSyntax `term :=
  ⟨Lean.Syntax.mkStrLit x.getId.toString⟩

namespace SyntaxRules

declare_syntax_cat syntaxRuleSpec
declare_syntax_cat syntaxRuleAtom

syntax str : syntaxRuleAtom
syntax ident ":" ident : syntaxRuleAtom
syntax ident ":" ident ":" num : syntaxRuleAtom

syntax "| " syntaxRuleAtom* " => " term : syntaxRuleSpec

syntax "syntax_rules " ident " quoted_by " str ident str " where" ppLine syntaxRuleSpec* : command

private def quoteStr (s : String) : String :=
  "\"" ++ s ++ "\""

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

private def startsWithChars : List Char -> List Char -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x == y && startsWithChars xs ys

private partial def replaceIdent (needle replacement input : String) : String :=
  let pat := needle.toList
  let rec go (prevIdent : Bool) : List Char -> List Char
    | [] => []
    | cs@(c :: rest) =>
        if !prevIdent && startsWithChars pat cs then
          let after := cs.drop pat.length
          match after with
          | d :: _ =>
              if isIdentChar d then
                c :: go (isIdentChar c) rest
              else
                replacement.toList ++ go false after
          | [] =>
              replacement.toList
        else
          c :: go (isIdentChar c) rest
  String.ofList (go false input.toList)

private partial def replaceAll (needle replacement input : String) : String :=
  let pat := needle.toList
  let rec go : List Char -> List Char
    | [] => []
    | cs@(c :: rest) =>
        if startsWithChars pat cs then
          replacement.toList ++ go (cs.drop pat.length)
        else
          c :: go rest
  if needle.isEmpty then input else String.ofList (go input.toList)

private structure Capture where
  name : String
  cat : String

private inductive Atom where
  | lit (text : String)
  | cap (capture : Capture) (prec : Option Nat)

private def expandCapture (cat : String) (c : Capture) : String :=
  if c.cat == cat then
    s!"${c.name}"
  else if c.cat == "ident" then
    s!"$(identStringTerm {c.name})"
  else
    s!"${c.name}"

private def parseSlots (captures : List Capture) : List (Capture × String) :=
  let rec go : Nat -> List Capture -> List (Capture × String)
    | _, [] => []
    | i, c :: cs => (c, s!"__syntax_rules_parse_{i}__") :: go (i + 1) cs
  go 0 captures

private def expandRhs (quoteName cat : String) (captures : List Capture) (rhs : Syntax) : CommandElabM String := do
  let some rhs := rhs.reprint
    | throwErrorAt rhs "could not reprint syntax-rule right-hand side"
  let objectCaptures := captures.filter (·.cat == cat)
  let parseSlots := parseSlots objectCaptures
  let rhs := parseSlots.foldl
    (fun s (c, slot) => replaceAll s!"parse {c.name}" slot s)
    rhs
  let rhs := captures.foldl
    (fun s c => replaceIdent c.name (expandCapture cat c) s)
    rhs
  return parseSlots.foldl
    (fun s (c, slot) => replaceAll slot s!"{quoteName}[ ${c.name} ]" s)
    rhs

private def elabCommandString (cmd : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command cmd (← getFileName) with
  | .ok stx => elabCommand stx
  | .error err => throwError "generated command did not parse:\n{cmd}\n\n{err}"

private def syntaxCat (cat : String) (c : Capture) : String :=
  if c.cat == cat then cat else c.cat

private def atomSyntax (cat : String) : Atom -> String
  | .lit text => quoteStr text
  | .cap capture none => syntaxCat cat capture
  | .cap capture (some prec) => s!"{syntaxCat cat capture}:{prec}"

private def atomPattern : Atom -> String
  | .lit text => text
  | .cap capture _ => s!"${capture.name}:{capture.cat}"

private def atomCaptures : Atom -> List Capture
  | .lit _ => []
  | .cap capture _ => [capture]

private def syntaxKeyword : List Atom -> String
  | .cap _ (some prec) :: _ => s!"syntax:{prec}"
  | _ => "syntax"

private def parseAtom (atom : Syntax) : CommandElabM Atom := do
  match atom with
  | `(syntaxRuleAtom| $text:str) =>
      return .lit text.getString
  | `(syntaxRuleAtom| $name:ident : $cat:ident) =>
      return .cap { name := name.getId.toString, cat := cat.getId.toString } none
  | `(syntaxRuleAtom| $name:ident : $cat:ident : $prec:num) =>
      return .cap { name := name.getId.toString, cat := cat.getId.toString } (some prec.getNat)
  | _ =>
      throwErrorAt atom "unsupported syntax-rule atom"

elab_rules : command
  | `(syntax_rules $catId:ident quoted_by $openQ:str $qcat:ident $closeQ:str where $rules:syntaxRuleSpec*) => do
      let cat := catId.getId.toString
      let quoteName := String.ofList openQ.getString.toList.dropLast
      let mut syntaxDecls : Array String := #[s!"declare_syntax_cat {cat}"]
      syntaxDecls := syntaxDecls.push
        s!"syntax {quoteStr openQ.getString} {qcat.getId} {quoteStr closeQ.getString} : term"
      let mut macroRules : Array String := #[]
      for rule in rules do
        match rule with
        | `(syntaxRuleSpec| | $atoms:syntaxRuleAtom* => $rhs:term) =>
            let atoms ← atoms.toList.mapM (fun atom => parseAtom atom.raw)
            let captures := atoms.flatMap atomCaptures
            syntaxDecls := syntaxDecls.push
              s!"{syntaxKeyword atoms} {String.intercalate " " (atoms.map (atomSyntax cat))} : {cat}"
            let rhs ← expandRhs quoteName cat captures rhs
            macroRules := macroRules.push
              s!"  | `({openQ.getString} {String.intercalate " " (atoms.map atomPattern)} {closeQ.getString}) => `({rhs})"
        | _ =>
            throwErrorAt rule "unsupported syntax_rules clause"
      for cmd in syntaxDecls do
        elabCommandString cmd
      elabCommandString <| "macro_rules\n" ++ "\n".intercalate macroRules.toList

end SyntaxRules

theorem idxOf?_cons_ne {ρ : List String} {x y : String}
  (h : y ≠ x)
  : (x :: ρ).idxOf? y = (ρ.idxOf? y).map fun n => n + 1 := by
  have : x ≠ y := by intro hxy; exact h hxy.symm
  simp [List.idxOf?, List.findIdx?, List.findIdx?.go, findIdx_go_succ, this]


instance {α : Type} {r : α -> α -> Prop} :
    Trans r r (Relation.ReflTransGen r) where
  trans h1 h2 := Relation.ReflTransGen.head h1 (Relation.ReflTransGen.single h2)

instance {α : Type} {r : α -> α -> Prop} :
    Trans r (Relation.ReflTransGen r) (Relation.ReflTransGen r) where
  trans h1 h2 := Relation.ReflTransGen.head h1 h2

instance {α : Type} {r : α -> α -> Prop} :
    Trans (Relation.ReflTransGen r) r (Relation.ReflTransGen r) where
  trans h1 h2 := h1.trans (Relation.ReflTransGen.single h2)

abbrev RelPullback {α β : Type} (f : α -> β) (r : β -> β -> Prop) : α -> α -> Prop :=
  fun x y => r (f x) (f y)

abbrev RelPullbackStar {α β : Type} (f : α -> β) (r : β -> β -> Prop) : α -> α -> Prop :=
  fun x y => Relation.ReflTransGen r (f x) (f y)

instance {α β : Type} {f : α -> β} {r : β -> β -> Prop} :
    Trans (RelPullback f r) (RelPullback f r) (RelPullbackStar f r) where
  trans h1 h2 := Relation.ReflTransGen.head h1 (Relation.ReflTransGen.single h2)

instance {α β : Type} {f : α -> β} {r : β -> β -> Prop} :
    Trans (RelPullback f r) (RelPullbackStar f r) (RelPullbackStar f r) where
  trans h1 h2 := Relation.ReflTransGen.head h1 h2

instance {α β : Type} {f : α -> β} {r : β -> β -> Prop} :
    Trans (RelPullbackStar f r) (RelPullback f r) (RelPullbackStar f r) where
  trans h1 h2 := h1.trans (Relation.ReflTransGen.single h2)

syntax "rt_step" "{" tacticSeq "}" : tactic
macro_rules
  | `(tactic| rt_step { $step:tacticSeq }) => `(tactic|
      exact Relation.ReflTransGen.single (by $step))

syntax "rt_repeat" "{" tacticSeq "}" : tactic
macro_rules
  | `(tactic| rt_repeat { $step:tacticSeq }) => `(tactic|
      first
      | exact Relation.ReflTransGen.refl
      | apply Relation.ReflTransGen.head
        · $step
        · rt_repeat { $step })
