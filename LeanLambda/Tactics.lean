import Lean

open Lean Elab Tactic

syntax casesOrLeft := ppLine "|" "inl" "=>" tacticSeq
syntax casesOrRight := ppLine "|" "inr" "=>" tacticSeq
syntax (name := casesOr)
  "cases_or " ":" term:51 " ∨ " term:51 " := " "by" tacticSeq
  casesOrLeft casesOrRight : tactic

elab_rules : tactic
  | `(tactic| cases_or : $p:term ∨ $q:term := by $proof:tacticSeq
      $leftAlt:casesOrLeft
      $rightAlt:casesOrRight) => do
      let leftSeq ← match leftAlt with
        | `(casesOrLeft| | inl =>%$_ $left:tacticSeq) => pure left
        | _ => throwUnsupportedSyntax
      let rightSeq ← match rightAlt with
        | `(casesOrRight| | inr =>%$_ $right:tacticSeq) => pure right
        | _ => throwUnsupportedSyntax
      evalTactic (← `(tactic|
        have h : $p ∨ $q := by
          ($proof:tacticSeq)))
      evalTactic (← `(tactic| rcases h with h | h))
      match ← getUnsolvedGoals with
      | leftGoal :: rightGoal :: rest =>
          setGoals [leftGoal]
          evalTactic leftSeq
          let leftGoals ← getUnsolvedGoals
          setGoals [rightGoal]
          evalTactic rightSeq
          let rightGoals ← getUnsolvedGoals
          setGoals (leftGoals ++ rightGoals ++ rest)
      | _ =>
          throwError "cases_or expected exactly two branch goals"

partial def obtainByConjuncts : Syntax -> MacroM Nat
  | `(term| $_ ∧ $q) => return 1 + (← obtainByConjuncts q)
  | _ => return 1

syntax "obtain_by " ident+ " : " term " := " term : tactic

macro_rules
  | `(tactic| obtain_by $xs:ident* : $p:term := $proof:term) => do
      let mut prop : TSyntax `term := p
      for x in xs.reverse do
        prop ← `(Exists (fun $x:ident => $prop))
      let n ← obtainByConjuncts p
      let mut facts : Array (TSyntax `ident) := #[]
      for i in [:n] do
        facts := facts.push (mkIdent (Name.mkSimple s!"h{i}"))
      `(tactic|
        set_option tactic.hygienic false in
        have ⟨$[$xs:ident],*, $[$facts:ident],*⟩ : $prop := ($proof))
