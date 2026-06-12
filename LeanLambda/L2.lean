import LeanLambda.L1
import LeanLambda.Tactics

set_option doc.verso true

/-!
This layer keeps the named terms from {lit}`L1` and adds simple types and typing
judgments.  The terms do not change; only the propositions we prove about them
become typed.

# Type Expressions

Types are base types and function types.  The notation {lit}`#A` creates a base type
named {lit}`A`, and {lit}`A ⇒ B` is the function type.

$$`
A ::= \alpha \mid A \to A
`

The Lean type below mirrors this grammar.  Function arrows associate to the
right, so {lit}`#A ⇒ #B ⇒ #C` means {lit}`#A ⇒ (#B ⇒ #C)`.
-/

inductive Ty where
  | base (x : String)
  | arr (dom cod : Ty)
deriving DecidableEq, Repr, Lean.ToExpr

syntax:max "#" ident : term
infixr:60 " ⇒ " => Ty.arr

macro_rules
  | `(#$X:ident) => do
      let X' : Lean.TSyntax `term := ⟨Lean.Syntax.mkStrLit X.getId.toString⟩
      `(Ty.base $X')

example : #A ⇒ #B ⇒ #C = #A ⇒ (#B ⇒ #C) := by rfl

namespace L2

/-!
# Typing Contexts

A context is a list of variable declarations.  Lookup returns the type assigned
to the first matching variable name.

$$`
\Gamma ::= \cdot \mid \Gamma, x : A
`

Contexts are lists, so the most recent declaration is checked first.  This
matches the usual convention that an inner binder shadows an outer one.
-/

abbrev Context := List (String × Ty)

def lookup (x : String) : Context -> Option Ty
  | [] => none
  | (y, A) :: Γ => if x = y then some A else lookup x Γ

/-!
# Typing Judgment

The judgment {lit}`Γ ⊢ e : A` is defined by the three usual rules: variables are
typed by lookup, lambdas introduce function types, and applications eliminate
function types.

$$`
\frac{x : A \in \Gamma}{\Gamma \vdash x : A}
\qquad
\frac{\Gamma, x : A \vdash e : B}{\Gamma \vdash \lambda x.\ e : A \to B}
`

$$`
\frac{\Gamma \vdash e_1 : A \to B \qquad \Gamma \vdash e_2 : A}
     {\Gamma \vdash e_1\ e_2 : B}
`

The inductive judgment below is exactly these three rules.  Proofs of typing
judgments are therefore derivation trees built from {lit}`var`, {lit}`lam`, and
{lit}`app`.
-/

inductive HasType : Context -> L1 -> Ty -> Prop where
  | var :
      lookup x Γ = some A ->
      HasType Γ (.var x) A
  | lam :
      HasType ((x, A) :: Γ) body B ->
      HasType Γ (.lam x body) (.arr A B)
  | app :
      HasType Γ fn (.arr A B) ->
      HasType Γ arg A ->
      HasType Γ (.app fn arg) B

notation:50 Γ " ⊢ " t " : " A => HasType Γ t A

/-!
The first examples are derivations of simple typing judgments.  They are small
enough that the proof scripts follow the inference rules directly.
-/

example : [("x", #A)] ⊢ L1[x] : #A := by
  apply HasType.var (by simp [lookup])

example : [] ⊢ L1.I : #A ⇒ #A := by
  unfold L1.I
  apply HasType.lam
  apply HasType.var (by simp [lookup])

example : [] ⊢ L1.T : #A ⇒ #B ⇒ #A := by
  unfold L1.T
  apply HasType.lam
  apply HasType.lam
  apply HasType.var (by simp [lookup])

example : [] ⊢ L1.F : #A ⇒ #B ⇒ #B := by
  unfold L1.F
  apply HasType.lam
  apply HasType.lam
  apply HasType.var (by simp [lookup])

example : [("y", #A)] ⊢ L1[(λx. x) y] : #A := by
  apply HasType.app (A := #A) (B := #A)
  . apply HasType.lam
    apply HasType.var (by simp [lookup])
  . apply HasType.var (by simp [lookup])

/-!
# Metatheory

The rest of the file records the first general facts about typing.  The visible
proof steps are intended to be mathematical statements; automation is used to
discharge the routine bookkeeping inside those steps.
-/

theorem typing_independent_of_context
  (hlookup : ∀x ∈ L1.FV e, lookup x Γ = lookup x Δ)
  (ht : Γ ⊢ e : A)
  : Δ ⊢ e : A :=
by
  induction ht generalizing Δ
  case var x Γ A h =>
      have : x ∈ L1.FV (L1.var x) := by
        rfl
      have : lookup x Δ = some A := by
        grind
      exact HasType.var this
  case lam x A Γ body B hbody ih =>
      have : ∀z ∈ L1.FV body,
          lookup z ((x, A) :: Γ) = lookup z ((x, A) :: Δ) := by
        intro z hz
        by_cases z = x
        · grind [lookup]
        · have : z ∈ L1.FV (L1.lam x body) := by
            exact ⟨hz, ‹z ≠ x›⟩
          grind [lookup]
      have : (x, A) :: Δ ⊢ body : B := by
        exact ih this
      exact HasType.lam this
  case app Γ fn A B arg htfn htarg ihfn iharg =>
      have : ∀z ∈ L1.FV fn, lookup z Γ = lookup z Δ := by
        intro z hz
        exact hlookup z (Or.inl hz)
      have : Δ ⊢ fn : A ⇒ B := by
        exact ihfn this
      have : ∀z ∈ L1.FV arg, lookup z Γ = lookup z Δ := by
        intro z hz
        exact hlookup z (Or.inr hz)
      have : Δ ⊢ arg : A := by
        exact iharg this
      exact HasType.app ‹Δ ⊢ fn : A ⇒ B› ‹Δ ⊢ arg : A›

theorem neutrality
  (hΓ : ∀x A B, lookup x Γ ≠ some (A ⇒ B))
  (hn : L1.Neutral e)
  (ht : Γ ⊢ e : A)
  : ∃x, e = L1.var x ∧ lookup x Γ = some A :=
by induction e generalizing Γ A <;> cases hn <;> cases ht <;> grind

theorem normal_arrow_is_lam
  (hΓ : ∀x A B, lookup x Γ ≠ some (A ⇒ B))
  (hn : L1.Normal e)
  (ht : Γ ⊢ e : A ⇒ B)
  : ∃x body, e = L1.lam x body ∧ L1.Normal body ∧ ((x, A) :: Γ) ⊢ body : B :=
by
  have            : ¬ L1.Neutral e                := by grind [neutrality]
  obtain_by x b   : e = L1.lam x b ∧ L1.Normal b  := by cases hn <;> grind
  have            : ((x, A) :: Γ) ⊢ b : B         := by cases ht <;> grind
  exists x, b

theorem boolean_normal_forms
  (hc : L1.Closed e)
  (hn : L1.Normal e)
  (ht : Γ ⊢ e : #α ⇒ #α ⇒ #α)
  : (e =α₁ L1.T) ∨ (e =α₁ L1.F)
:= by
  have : [] ⊢ e : #α ⇒ #α ⇒ #α
  := by grind [typing_independent_of_context, L1.Closed, L1.FV, L0.Closed]

  obtain_by x y e₂ : e = L1[λ{x}. λ{y}. {e₂}] ∧ L1.Normal e₂ ∧ [(y, #α), (x, #α)] ⊢ e₂ : #α
  := by grind [normal_arrow_is_lam, lookup]

  have : L1.Neutral e₂
  := by cases ‹[(y, #α), (x, #α)] ⊢ e₂ : #α› <;> cases ‹L1.Normal _› <;> assumption

  obtain_by z : e₂ = L1.var z ∧ lookup z [(y, #α), (x, #α)] = some #α
  := by grind [neutrality, lookup]

  cases_or : (z = x) ∨ (z = y) := by grind [lookup]
  | inl =>
      by_cases x = y
      · right; unfold L1.F; alpha_eq
      · left; unfold L1.T; alpha_eq
  | inr =>
      right; unfold L1.F; alpha_eq

theorem progress_in
  (ht : Γ ⊢ e : A)
  : L1.Normal e ∨ L1.ReducibleIn ρ e :=
by
  induction ht generalizing ρ
  case var x _ _ _ =>
      have : L1.Normal (L1.var x) := by solve_by_elim [L1.Normal.neutral, L1.Neutral.var]
      grind
  case lam x _ _ body _ _ ih =>
      cases_or : (L1.Normal body) ∨ (L1.ReducibleIn (x :: ρ) body) := by grind
      | inl =>
        have : L1.Normal (L1.lam x body) := by solve_by_elim [L1.Normal.lam]
        grind
      | inr =>
        have : L1.ReducibleIn ρ (L1.lam x body) := by
          simp_all [L1.ReducibleIn, L1.toL0With]
          aesop (add safe constructors Exists, safe constructors L0.BetaStep)
        grind
  case app _ fn _ _ arg _ _ ihfn iharg =>
      cases_or : (L1.Normal fn) ∨ (L1.ReducibleIn ρ fn) := by grind
      | inl =>
        cases_or : (L1.Normal arg) ∨ (L1.ReducibleIn ρ arg) := by grind
        | inl =>
          cases ‹L1.Normal fn› with
          | neutral =>
              have : L1.Normal (L1.app fn arg) := by
                solve_by_elim [L1.Normal.neutral, L1.Neutral.app]
              grind
          | @lam b x nb =>
              have : L1.ReducibleIn ρ ((L1.lam x b).app arg) := by
                simp_all [L1.ReducibleIn, L1.toL0With]
                aesop (add safe constructors Exists, safe apply L0.BetaStep.beta)
              grind
        | inr =>
          have : L1.ReducibleIn ρ (L1.app fn arg) := by
            simp_all [L1.ReducibleIn, L1.toL0With]
            aesop (add safe constructors Exists, safe apply L0.BetaStep.app_right)
          grind
      | inr =>
        have : L1.ReducibleIn ρ (L1.app fn arg) := by
          simp_all [L1.ReducibleIn, L1.toL0With]
          aesop (add safe constructors Exists, safe apply L0.BetaStep.app_left)
        grind


end L2
