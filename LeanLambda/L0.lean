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

Substitution has to pass under binders.  The auxiliary function {lit}`mapVars`
records how many binders we have crossed with the {lit}`cutoff` argument.  Shifting
then changes only the variables at or above that cutoff.
-/

def mapVars (cutoff: Nat) (onVar : Nat -> Nat -> L0): L0 -> L0
  | .var k => onVar cutoff k
  | .free x => .free x
  | .lam body => .lam (mapVars (cutoff + 1) onVar body)
  | .app f a => .app (mapVars cutoff onVar f) (mapVars cutoff onVar a)

def ShiftAbove (d cutoff : Nat) : L0 -> L0 :=
  mapVars cutoff (λc k => .var (if k < c then k else (k + d)))

def ShiftDownAbove (cutoff : Nat) : L0 -> L0 :=
  mapVars cutoff (λc k => .var (if k < c then k else (k - 1)))

def Shift (d : Nat) : L0 -> L0 := ShiftAbove d 0

def ShiftDown : L0 -> L0 := ShiftDownAbove 0

def Subst (j : Nat) (s : L0) : L0 -> L0 :=
  mapVars 0 (λc k => if k = j + c then Shift c s else .var k)

def SubstTop (s body : L0) : L0 :=
  ShiftDown (Subst 0 (Shift 1 s) body)

/-!
The basic substitution facts below say what top-level substitution does to
variables.  They are the calculation rules used by beta reduction examples.
-/

theorem shiftAbove_zero : ShiftAbove 0 cutoff t = t := by
  induction t generalizing cutoff <;> simp_all [ShiftAbove, mapVars]

theorem shiftDown_shiftAbove
  : ShiftDownAbove cutoff (ShiftAbove 1 cutoff t) = t := by
  induction t generalizing cutoff with
  | var k =>
      simp [ShiftDownAbove, ShiftAbove, mapVars]
      by_cases h : k < cutoff <;> simp [h]
      omega
  | _ => simp_all [ShiftDownAbove, ShiftAbove, mapVars]

theorem substTop_var_zero : SubstTop s (.var 0) = s := by
  simp [SubstTop, Subst, mapVars, Shift, shiftAbove_zero, ShiftDown, shiftDown_shiftAbove]

theorem substTop_var_succ : SubstTop s (.var (n + 1)) = .var n := by
  simp [SubstTop, Subst, ShiftDown, ShiftDownAbove, mapVars]

theorem substTop_free : SubstTop s (.free x) = .free x := by
  rfl

/-!
# Free Variables

The set given by {lit}`FV` contains exactly the named variables that occur free in a term.
De Bruijn variables are bound-variable references, so they contribute no free
names.
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
-/

inductive BetaStep : L0 -> L0 -> Prop where
  | beta :
      BetaStep (.app (.lam body) arg) (SubstTop arg body)
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
