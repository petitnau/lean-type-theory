import LeanLambda.L0

set_option doc.verso true

/-!
The second layer restores the syntax that we normally write on paper: variables
have names, and lambda abstractions bind names.  The semantics of this layer is
still given by {lit}`L0`; named terms are translated to de Bruijn terms before we
state alpha equivalence and beta reduction.

# Named Syntax

The datatype {lit}`L1` is the named abstract syntax tree.  The notation {lit}`L1[...]`
lets examples use lambda-calculus syntax while still elaborating to this
datatype.

$$`
e ::= x \mid \lambda x.\ e \mid e\ e
`

This is the syntax students usually write on paper.  The constructors keep the
names explicitly, before any quotienting by alpha-equivalence.
-/

inductive L1 where
  | var (x : String)
  | lam (x : String) (body : L1)
  | app (fn arg : L1)
deriving DecidableEq, Repr, Lean.ToExpr

syntax_rules l1Term quoted_by "L1[" l1Term "]" where
  | "{" t:term "}"                      => t
  | "(" t:l1Term ")"                    => parse t
  | x:ident                             => L1.var x
  | "λ" x:ident "." body:l1Term         => L1.lam x (parse body)
  | "λ" "{" x:term "}" "." body:l1Term  => L1.lam x (parse body)
  | f:l1Term:70 a:l1Term:71             => L1.app (parse f) (parse a)

example : L1[λx. x] = L1.lam "x" (L1.var "x") := by rfl
example : L1[x y z] = L1[(x y) z] := by rfl

/-!
# Meaning in {lit}`L0`

The context {lit}`ctx` records the binders currently in scope.  A variable whose
name appears in the context becomes a de Bruijn index; otherwise it remains a
named free variable.

$$`
\begin{array}{rcl}
\llbracket x \rrbracket_\rho
  &=& \begin{cases}
      n & \rho(n) = x\\
      x & x \notin \rho
      \end{cases}\\
\llbracket \lambda x.\ e \rrbracket_\rho
  &=& \lambda.\ \llbracket e \rrbracket_{x,\rho}\\
\llbracket e_1\ e_2 \rrbracket_\rho
  &=& \llbracket e_1 \rrbracket_\rho\ \llbracket e_2 \rrbracket_\rho
\end{array}
`

The translation resolves a bound variable by its position in the context.  Free
variables are left as names, so open terms can still be represented.
-/

namespace L1

def toL0With (ctx : List String) : L1 -> L0
  | .var x =>
      (ctx.idxOf? x).elim (.free x) (.var)
  | .lam x body =>
      .lam (toL0With (x :: ctx) body)
  | .app fn arg =>
      .app (toL0With ctx fn) (toL0With ctx arg)
def toL0 (t : L1) : L0 := toL0With [] t

/-!
Free variables are defined structurally on named terms.  The theorem
{lit}`fv_toL0With` connects this visible definition to the free variables of the
translated {lit}`L0` term.

$$`
\begin{array}{rcl}
FV(x) &=& \{x\}\\
FV(\lambda x.\ e) &=& FV(e) \setminus \{x\}\\
FV(e_1\ e_2) &=& FV(e_1) \cup FV(e_2)
\end{array}
`

Unlike {lit}`L0`, a lambda removes its bound name from the free-variable set.
The theorem following the definition says that this agrees with the translation
to {lit}`L0`.
-/

def FV : L1 -> Set String
  | .var x => {y | y = x}
  | .lam x body => {y | y ∈ FV body ∧ y ≠ x}
  | .app fn arg => {y | y ∈ FV fn ∨ y ∈ FV arg}
def Closed (t : L1) : Prop :=
  ∀ x, x ∉ FV t

/-!
Two named terms are alpha-equivalent when they translate to the same de Bruijn
term.  The versions with environments are useful when the comparison happens
under binders.

$$`
e =_\alpha e' \quad\text{iff}\quad
\llbracket e \rrbracket_\cdot = \llbracket e' \rrbracket_\cdot
`

In this development, alpha-equivalence is not another recursive relation on
names.  It means that the two terms have the same de Bruijn meaning.
-/

def AlphaEqWith (ρ ρ' : List String) (s t : L1) : Prop :=
  toL0With ρ s = toL0With ρ' t
def AlphaEqIn (ρ : List String) (s t : L1) : Prop :=
  AlphaEqWith ρ ρ s t
def AlphaEq (s t : L1) : Prop :=
  AlphaEqIn [] s t
infix:50 " =α₁ " => L1.AlphaEq
local infix:50 " =α " => L1.AlphaEq

abbrev BetaStep (s t : L1) : Prop := (toL0 s) →β₀ (toL0 t)
infix:50 " →β₁ " => BetaStep
local infix:50 " →β " => BetaStep

abbrev BetaStar (s t : L1) : Prop := (toL0 s) →β₀* (toL0 t)
infix:50 " →β₁* " => BetaStar
local infix:50 " →β* " => BetaStar

def NormalForm (t : L1) : Prop := L0.NormalForm (toL0 t)

/-!
The {lit}`alpha_eq` tactic checks these small alpha-equivalence goals by reducing
both sides to {lit}`L0`.
-/

syntax "alpha_eq" : tactic
macro_rules
  | `(tactic| alpha_eq) =>
      `(tactic|
        simp_all [_root_.L1.AlphaEq, _root_.L1.AlphaEqIn, _root_.L1.AlphaEqWith,
          _root_.L1.toL0, _root_.L1.toL0With,
          List.idxOf?, List.findIdx?, List.findIdx?.go] <;> grind)

/-!
# Named Reduction Rules

The relation {lit}`ReduceIn` presents beta reduction directly over named syntax.
Its substitution premise is still checked by translating the redex to {lit}`L0`,
which avoids implementing a separate fresh-name algorithm here.

$$`
\frac{[e_2/x]e_1 = e'}{(\lambda x.\ e_1)\ e_2 \longrightarrow e'}
\qquad
\frac{e \longrightarrow e'}{\lambda x.\ e \longrightarrow \lambda x.\ e'}
`

$$`
\frac{e_1 \longrightarrow e_1'}{e_1\ e_2 \longrightarrow e_1'\ e_2}
\qquad
\frac{e_2 \longrightarrow e_2'}{e_1\ e_2 \longrightarrow e_1\ e_2'}
`

These rules are the named presentation of reduction.  The beta rule delegates
the substitution check to {lit}`L0`, and the soundness theorem below connects
the named relation back to beta reduction on meanings.
-/

def SubstIn (ρ : List String) (x : String) (arg body out : L1) : Prop :=
  L0.subst 0 (toL0With ρ arg) (toL0With (x :: ρ) body) = toL0With ρ out

def Subst (x : String) (arg body out : L1) : Prop :=
  SubstIn [] x arg body out

inductive ReduceIn : List String -> L1 -> L1 -> Prop where
  | beta :
      SubstIn ρ x arg body out ->
      ReduceIn ρ (.app (.lam x body) arg) out
  | lam :
      ReduceIn (x :: ρ) body body' ->
      ReduceIn ρ (.lam x body) (.lam x body')
  | app_left :
      ReduceIn ρ fn fn' ->
      ReduceIn ρ (.app fn arg) (.app fn' arg)
  | app_right :
      ReduceIn ρ arg arg' ->
      ReduceIn ρ (.app fn arg) (.app fn arg')

def Reduce : L1 -> L1 -> Prop := ReduceIn []
def ReduceStar : L1 -> L1 -> Prop := Relation.ReflTransGen Reduce

theorem StepIn.toBetaStep : ReduceIn ρ e e' -> L1.toL0With ρ e →β₀ L1.toL0With ρ e' := by
  intro h; induction h <;> grind [toL0With, SubstIn, L0.BetaStep]

theorem Step.toBetaStep : Reduce e e' ->  L1.toL0 e →β₀ L1.toL0 e' :=
  @StepIn.toBetaStep [] _ _

theorem Reduce.sound: Reduce e e' -> e →β₁ e' :=
  Step.toBetaStep

theorem ReduceStar.sound : ReduceStar e e' -> e →β₁* e' := by
  intro h; induction h <;> grind [Reduce.sound]

infix:50 " ⟶₁ " => Reduce
infix:50 " ⟶₁* " => ReduceStar

/-!
# Reducibility

A term is reducible when its {lit}`L0` meaning can take a beta step.  The contextual
form {lit}`ReducibleIn` is used when reasoning under named binders.
-/

def ReducibleIn (ρ : List String) (e : L1) : Prop :=
  ∃ e', L1.toL0With ρ e →β₀ e'

def Reducible (e : L1) : Prop :=
  ReducibleIn [] e

/-!
# Normal and Neutral Terms

The inductive predicates {lit}`Normal` and {lit}`Neutral` describe the normal forms of
the named language.  A lambda is normal when its body is normal; a neutral term
is a variable applied to normal arguments.

$$`
\frac{e\ \mathsf{normal}}{\lambda x.\ e\ \mathsf{normal}}
\qquad
\frac{e\ \mathsf{neutral}}{e\ \mathsf{normal}}
`

$$`
\frac{}{x\ \mathsf{neutral}}
\qquad
\frac{e_1\ \mathsf{neutral} \qquad e_2\ \mathsf{normal}}
     {e_1\ e_2\ \mathsf{neutral}}
`

This mutual definition separates introduction forms from stuck computations:
lambdas are normal directly, while neutral terms are variables applied to normal
arguments.
-/

mutual

inductive Normal : L1 -> Prop where
  | lam :
      Normal body ->
      Normal (.lam x body)
  | neutral :
      Neutral e ->
      Normal e

inductive Neutral : L1 -> Prop where
  | var :
      Neutral (.var x)
  | app :
      Neutral fn ->
      Normal arg ->
      Neutral (.app fn arg)

end

/-!
# Examples

The named constants mirror the {lit}`L0` constants, but can now be written with
ordinary variable names.
-/

def I : L1 := L1[λx. x]
def T : L1 := L1[λx. λy. x]
def F : L1 := L1[λx. λy. y]

def N : L1 := L1[λb. b {F} {T}]
def N' : L1 := L1[λb. λx. λy. b y x]
def A : L1 := L1[λb. λc. b c {F}]
def M : L1 := L1[λb. λx. λy. y b x]

def Z : L1 := L1[λf. λx. x]
def S : L1 := L1[λn. λf. λx. f (n f x)]
def Plus : L1 := L1[λn. λm. n {S} m]

example : L1.toL0 L1[λx. x] = L0[λ 0] := by rfl
example : L1.toL0 L1[λx. λy. x] = L0[λ λ 1] := by rfl
example : L1.toL0 L1[λx. λy. y] = L0[λ λ 0] := by rfl
example : L1.toL0 L1[λx. λx. x] = L0[λ λ 0] := by rfl

example : L1.toL0 L1[x] = L0[x] := by rfl

example : L1[λx. x] =α L1[λy. y] := by alpha_eq
example : L1[(λx. x) (λy. y)] →β L1[λz. z] := by beta_step
example : L1[(λx. x) (λy. y)] →β* L1[λz. z] := by beta_steps

example : L1.NormalForm I := by normal
example : L1.NormalForm T := by normal
example : L1.NormalForm F := by normal
example : L1.NormalForm N := by normal
example : L1.NormalForm N' := by normal
example : L1.NormalForm A := by normal
example : L1.NormalForm M := by normal

example : L1[{I} x] →β L1[x] := by beta_step
example : L1[{I} x] →β* L1[x] := by rt_step { beta_step }
example : L1[{T} x y] →β* L1[x] := by beta_steps
example : L1[{F} x y] →β* L1[y] := by beta_steps

example : L1[{N} {F}] →β* L1[{T}] := by calc
    _   = L1[{N} {F}] := by rfl
    _   = L1[(λb. b {F} {T}) {F}] := by rfl
    _  →β L1[{F} {F} {T}] := by beta_step
    _   = L1[(λx. λy. y) {F} {T}] := by rfl
    _  →β L1[(λy. y) {T}] := by beta_step
    _  →β L1[{T}] := by beta_step

example : L1[{N} {T}] →β* L1[{F}] := by calc
    _   = L1[{N} {T}] := by rfl
    _   = L1[(λb. b {F} {T}) {T}] := by rfl
    _  →β L1[{T} {F} {T}] := by beta_step
    _   = L1[(λx. λy. x) {F} {T}] := by rfl
    _  →β L1[(λy. {F}) {T}] := by beta_step
    _  →β L1[{F}] := by beta_step

example : L1[{N} {F}] →β* L1[{T}] := by calc
    _   = L1[{N} {F}] := by rfl
    _   = L1[(λb. b {F} {T}) {F}] := by rfl
    _  →β L1[{F} {F} {T}] := by beta_step
    _   = L1[(λx. λy. y) {F} {T}] := by rfl
    _  →β L1[(λy. y) {T}] := by beta_step
    _  →β L1[{T}] := by beta_step

example : L1[{N'} {T}] →β* L1[{F}] := by beta_steps
example : L1[{N'} {F}] →β* L1[{T}] := by beta_steps

example : L1[{N} {T}] →β* L1[{F}] := by beta_steps
example : L1[{N} {F}] →β* L1[{T}] := by beta_steps
example : L1[{N'} {T}] →β* L1[{F}] := by beta_steps
example : L1[{N'} {F}] →β* L1[{T}] := by beta_steps
example : L1[{A} {T} {T}] →β* L1[{T}] := by beta_steps
example : L1[{A} {T} {F}] →β* L1[{F}] := by beta_steps
example : L1[{A} {F} {T}] →β* L1[{F}] := by beta_steps
example : L1[{A} {F} {F}] →β* L1[{F}] := by beta_steps

example : L1[(λx. x) y] ⟶₁ L1[y] := by
  apply L1.ReduceIn.beta
  rfl

example : L1[(λx. x) y] ⟶₁* L1[y] := by
  rt_step {
    apply L1.ReduceIn.beta
    rfl
  }

example : Normal L1[λx. x] := by
  apply Normal.lam
  apply Normal.neutral
  apply Neutral.var

example : Neutral L1[x y] := by
  apply Neutral.app
  · apply Neutral.var
  · apply Normal.neutral
    apply Neutral.var

end L1
