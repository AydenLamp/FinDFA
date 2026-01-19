import MyProject.DFA.Minimize

/-!
# Minimization of DFAs examples

This file defines some specific DFAs, with Fin instances and Fintype and DecidableEq instances on
their state spaces and alphabets, and computes their minimal DFAs using `DFA.minimize`.
-/

open DFA

inductive α : Type
  | a
  | b
deriving DecidableEq, Fintype

open α

inductive σ₁ : Type
  | s₁
  | s₂
deriving DecidableEq, Fintype

def M₁ : DFA α σ₁ where
  step (s : σ₁) (x : α) :=
      match s, x with
      -- (s₁, a) goes to s₂
      | σ₁.s₁, a => σ₁.s₂
      -- loop on b in s₁
      | σ₁.s₁, b => σ₁.s₁
      -- (s₂, a) goes to s₁
      | σ₁.s₂, a => σ₁.s₁
      -- loop on b in s₂
      | σ₁.s₂, b => σ₁.s₂
  start := σ₁.s₁
  accept := {σ₁.s₂}

#eval M₁.eval [b, a, b]

inductive σ₃ : Type
  | s₁
  | s₂
  | s₃
  | s₄
  | s₅
  | s₆
  | s₇
  | s₈
deriving DecidableEq, Fintype

def M₃ : DFA α σ₃ where
  step (s : σ₃) (x : α) :=
      match s, x with
      | σ₃.s₁, a => σ₃.s₂
      | σ₃.s₁, b => σ₃.s₃
      | σ₃.s₂, a => σ₃.s₅
      | σ₃.s₂, b => σ₃.s₄
      | σ₃.s₃, a => σ₃.s₄
      | σ₃.s₃, b => σ₃.s₁
      | σ₃.s₄, a => σ₃.s₇
      | σ₃.s₄, b => σ₃.s₂
      | σ₃.s₅, a => σ₃.s₆
      | σ₃.s₅, b => σ₃.s₇
      | σ₃.s₆, a => σ₃.s₁
      | σ₃.s₆, b => σ₃.s₈
      | σ₃.s₇, a => σ₃.s₈
      | σ₃.s₇, b => σ₃.s₅
      | σ₃.s₈, a => σ₃.s₃
      | σ₃.s₈, b => σ₃.s₆
  start := σ₃.s₁
  accept := {σ₃.s₄, σ₃.s₈}

#eval M₃.eval [α.a, α.b, α.a, α.a, α.b]

instance : Fin M₃ where
  finAccept := {σ₃.s₄, σ₃.s₈}
  accept_eq := by simp

instance : DecidableRel (M₃.nerodeEquiv) := by
  infer_instance
/-- Decidability instance for testing if two states of a Fin DFA are
Nerode equivalent. -/
instance nerode_decidable : DecidableRel (M.nerodeEquiv) := by
  intros s₁ s₂
  apply decidable_of_decidable_of_iff (M.boundedNerode_iff_nerode s₁ s₂)
#eval M₃.nerodeEquiv σ₃.s₁ σ₃.s₅
