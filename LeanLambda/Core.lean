import Mathlib.Logic.Relation

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
