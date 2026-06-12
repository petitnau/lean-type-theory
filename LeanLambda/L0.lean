import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import LeanLambda.Core

set_option doc.verso true

/-!
This first language is the computational core used by the later chapters.
Bound variables are represented by de Bruijn indices, while free variables keep
their names.  This makes substitution and beta reduction executable as ordinary
recursive definitions without having to choose fresh names.

# Syntax

The terms of {lit}`L0` are variables, free variables, lambda abstractions, and
applications.

$$`
e ::= n \mid x \mid \lambda.\ e \mid e\ e
`

The Lean datatype below has one constructor for each form in this grammar.
-/

inductive L0 where
  | var (x : Nat)
  | free (x : String)
  | lam (body : L0)
  | app (fn arg : L0)
deriving DecidableEq, Repr, Lean.ToExpr

declare_syntax_cat l0Term
syntax    "L0[" l0Term "]" : term
syntax    "{" term "}" : l0Term
syntax    "(" l0Term ")" : l0Term
syntax    "λ" l0Term : l0Term
syntax    num : l0Term
syntax    ident : l0Term
syntax:70 l0Term:70 l0Term:71 : l0Term

macro_rules
  | `(L0[ $n:num ]) => `(L0.var $n)
  | `(L0[ $x:ident ]) => do
      let x' : Lean.TSyntax `term := ⟨Lean.Syntax.mkStrLit x.getId.toString⟩
      `(L0.free $x')
  | `(L0[ { $t:term } ]) => `($t)
  | `(L0[ ( $t:l0Term ) ]) => `(L0[ $t ])
  | `(L0[ λ $body:l0Term ]) => `(L0.lam L0[ $body ])
  | `(L0[ $f:l0Term $a:l0Term ]) => `(L0.app L0[ $f ] L0[ $a ])

example : L0[λ λ 1] = L0.lam (L0.lam (L0.var 1)) := by rfl
example : L0[x]     = L0.free "x" := by rfl
example : L0[0 1 2] = L0.app (L0.app (L0.var 0) (L0.var 1)) (L0.var 2) := by rfl

namespace L0

/-!
# Substitution

Substitution has to pass under binders.  When we cross a binder, the term being
substituted must be shifted so that its free de Bruijn indices still refer to
the same binders.

$$`
\begin{array}{rcl}
\uparrow_c(n) &=& \begin{cases}
  n & n < c\\
  n+1 & n \ge c
\end{cases}\\
\uparrow_c(x) &=& x\\
\uparrow_c(\lambda.\ e) &=& \lambda.\ \uparrow_{c+1}(e)\\
\uparrow_c(e_1\ e_2) &=& \uparrow_c(e_1)\ \uparrow_c(e_2)
\end{array}
`

The cutoff tells the shift operation which indices are protected by binders we
have already crossed.  The recursive definition below follows the displayed
equations directly.
-/

def shiftAbove (cutoff : Nat) : L0 -> L0
  | .var k => .var (if k < cutoff then k else k + 1)
  | .free x => .free x
  | .lam body => .lam (shiftAbove (cutoff + 1) body)
  | .app f a => .app (shiftAbove cutoff f) (shiftAbove cutoff a)

def subst (j : Nat) (s : L0) : L0 -> L0
  | .var k =>
      if k = j then s
      else if j < k then .var (k - 1)
      else .var k
  | .free x => .free x
  | .lam body => .lam (subst (j + 1) (shiftAbove 0 s) body)
  | .app f a => .app (subst j s f) (subst j s a)

/-!
The basic substitution facts below say what substitution for the outermost
variable does to variables.  They are the calculation rules used by beta
reduction examples.

$$`
\begin{array}{rcl}
[s/0]0 &=& s\\
[s/0](n+1) &=& n\\
[s/j]x &=& x
\end{array}
`

General substitution is defined above, but these three equations are the cases
that show up most often when contracting a redex at the outermost binder.
-/

theorem subst_var_zero : subst 0 s (.var 0) = s := by rfl

theorem subst_var_succ : subst 0 s (.var (n + 1)) = .var n := by rfl

theorem subst_free : subst j s (.free x) = .free x := by rfl

/-!
# Free Variables

The set given by {lit}`FV` contains exactly the named variables that occur free in a term.
De Bruijn variables are bound-variable references, so they contribute no free
names.

$$`
\begin{array}{rcl}
FV(n) &=& \varnothing\\
FV(x) &=& \{x\}\\
FV(\lambda.\ e) &=& FV(e)\\
FV(e_1\ e_2) &=& FV(e_1) \cup FV(e_2)
\end{array}
`

This definition tracks only named free variables.  Bound de Bruijn indices are
not names, so they cannot contribute to this set.
-/

def FV : L0 -> Set String
  | .var _    => {}
  | .free x   => {x}
  | .lam body => (FV body)
  | .app f a  => (FV f) ∪ (FV a)

def Closed (t : L0) : Prop :=
  ∀ x, x ∉ FV t

example : "x" ∈ FV L0[x] := by rfl
example : Closed L0[λ 0] := by intro _ h; exact h

/-!
# Beta Reduction

A beta step contracts one redex or performs one such contraction inside an
application or a lambda.  The reflexive-transitive closure {lit}`BetaStar` is the
many-step reduction relation.

$$`
\frac{}{(\lambda.\ e)\ e' \to_\beta [e'/0]e}
\qquad
\frac{e_1 \to_\beta e_1'}{e_1\ e_2 \to_\beta e_1'\ e_2}
\qquad
\frac{e_2 \to_\beta e_2'}{e_1\ e_2 \to_\beta e_1\ e_2'}
\qquad
\frac{e \to_\beta e'}{\lambda.\ e \to_\beta \lambda.\ e'}
`

The first rule is the actual contraction rule.  The other three rules say that
one contraction may happen in any immediate subterm.

$$`
\frac{}{e \to_\beta^* e}
\qquad
\frac{e \to_\beta e' \qquad e' \to_\beta^* e''}{e \to_\beta^* e''}
`

The many-step relation is Lean's reflexive-transitive closure of one beta step.
-/

inductive BetaStep : L0 -> L0 -> Prop where
  | beta :
      BetaStep (.app (.lam body) arg) (subst 0 arg body)
  | app_left :
      BetaStep f f' ->
      BetaStep (.app f a) (.app f' a)
  | app_right :
      BetaStep a a' ->
      BetaStep (.app f a) (.app f a')
  | lam :
      BetaStep body body' ->
      BetaStep (.lam body) (.lam body')
infix:50 " →β₀ " => BetaStep
local infix:50 " →β " => BetaStep

abbrev BetaStar : L0 -> L0 -> Prop := Relation.ReflTransGen BetaStep
infix:50 " →β₀* " => BetaStar
local infix:50 " →β* " => BetaStar

def NormalForm (t : L0) : Prop := ∀u, ¬(t →β u)

syntax "beta_step" : tactic
macro_rules | `(tactic| beta_step) =>  `(tactic| repeat' constructor)
syntax "beta_steps" : tactic
macro_rules | `(tactic| beta_steps) => `(tactic| rt_repeat { beta_step })
syntax "normal" : tactic
macro_rules | `(tactic| normal) => `(tactic| intro _ _; repeat' cases ‹BetaStep _ _›)

/-!
# Examples

The usual lambda-calculus constants are represented directly as {lit}`L0` terms.
The examples after the definitions are checked reduction derivations.
-/

def I : L0 := L0[λ 0]
def T : L0 := L0[λ λ 1]
def F : L0 := L0[λ λ 0]

def N : L0 := L0[λ 0 {F} {T}]
def N' : L0 := L0[λ λ λ 2 0 1]
def A : L0 := L0[λ λ 1 0 {F}]
def M : L0 := L0[λ λ λ 0 2 1]

example : NormalForm I := by normal
example : NormalForm T := by normal
example : NormalForm F := by normal
example : NormalForm N := by normal
example : NormalForm N' := by normal
example : NormalForm A := by normal
example : NormalForm M := by normal

example : L0[{I} 3] →β L0[3] := by beta_step
example : L0[{I} 3] →β* L0[3] := by rt_step { beta_step }
example : L0[{T} 3 4] →β* L0[3] := by beta_steps
example : L0[{F} 3 4] →β* L0[4] := by beta_steps

example : L0[{N} {T}] →β* L0[{F}] := by calc
    _   = L0[{N} {T}] := by rfl
    _   = L0[(λ 0 {F} {T}) {T}] := by rfl
    _  →β L0[{T} {F} {T}] := by beta_step
    _   = L0[(λ λ 1) {F} {T}] := by rfl
    _  →β L0[(λ {F}) {T}] := by beta_step
    _  →β L0[{F}] := by beta_step

example : L0[{N} {F}] →β* L0[{T}] := by calc
    _   = L0[{N} {F}] := by rfl
    _   = L0[(λ 0 {F} {T}) {F}] := by rfl
    _  →β L0[{F} {F} {T}] := by beta_step
    _   = L0[(λ λ 0) {F} {T}] := by rfl
    _  →β L0[(λ 0) {T}] := by beta_step
    _  →β L0[{T}] := by beta_step

example : L0[{N'} {T}] →β* L0[{F}] := by beta_steps
example : L0[{N'} {F}] →β* L0[{T}] := by beta_steps

example : L0[{N} {T}] →β* L0[{F}] := by beta_steps
example : L0[{N} {F}] →β* L0[{T}] := by beta_steps
example : L0[{N'} {T}] →β* L0[{F}] := by beta_steps
example : L0[{N'} {F}] →β* L0[{T}] := by beta_steps
example : L0[{A} {T} {T}] →β* L0[{T}] := by beta_steps
example : L0[{A} {T} {F}] →β* L0[{F}] := by beta_steps
example : L0[{A} {F} {T}] →β* L0[{F}] := by beta_steps
example : L0[{A} {F} {F}] →β* L0[{F}] := by beta_steps

def Z : L0 := L0[λ λ 0]
def S : L0 := L0[λ λ λ 1 (2 1 0)]
def Plus : L0 := L0[λ λ 1 {S} 0]

end L0
