import MyProject.Defs

/-!
# Morphisms between DFAs

This file defines morphisms between DFAs, which are bundled functions between the state spaces
that respect the transition function, start state, and accept states of the DFAs.

We then define a partial order on `AccessibleFinDFA`s where `M ≤ N` iff there exists a surjective
morphism from `N.toDFA` to `M.toDFA`.

## Main definitions

* `DFA.Hom` - A morphism from the `DFA` `M` to the `DFA` `N`, notated `M →ₗ N`.

* `DFA.Equiv` - An equivalence of `DFA`s, which is a bijective morphism, notated `M ≃ₗ N`.

* `AccessibleFinDFA.HomSurj` - A morphism on the underlying `DFA`s of the `AccessibleFinDFA`s
  that is surjective on states. Notated `M ↠ N`.

* `AccessibleFinDFA.le` - Notated `≤`, the partial order on `AccessibleFinDFA`s.

* `AccessibleFinDFA.IsMinimal` - A predicate that `M` is minimal by the partial order, up to
  equivalence of the underlying `DFA`s.

## Main theorems

* `DFA.Hom.pres_lang` - `M.accepts = N.accepts` when there exists `f : M →ₗ N`.
* `AccessibleFinDFA.le_refl` - Reflexivity of `≤`.
* `AccessibleFinDFA.le_trans` - Transitivity of `≤`.
* `AccessibleFinDFA.le_antisymm` - Antisymmetry of `≤` up to equivalence of underlying DFAs.

## Notation

* `M →ₗ N` - Notation for `DFA.Hom M N`.
* `M ≃ₗ N` - Notation for `DFA.Equiv M N`.
* `M ↠ N` - Notation for `AccessibleFinDFA.HomSurj M N`.
* `M ≤ N` - Notation for the partial order on `AccessibleFinDFA`s.

## Blueprint

* One DEF entry for `DFA.Hom` and `DFA.Equiv`.
Label : dfa-hom
Lean defs : `DFA.Hom`, `DFA.Equiv`
Content : explain the structures
Dependencies : dfa

* One DEF entry for the partial order on `AccessibleFinDFA`s.
Label : accessible-fin-dfa-le
Lean defs : `AccessibleFinDFA.HomSurj`
`AccessibleFinDFA.le`
`AccessibleFinDFA.le_refl`
`AccessibleFinDFA.le_trans`
`AccessibleFinDFA.le_antisymm`
`AccessibleFinDFA.isMinimal`
Content : explain how we can define a partial order on `AccessibleFinDFA`s by the
existence of a surjective morphism between their underlying DFAs. Prove that this is
a partial order up to equivalence of the underlying DFAs.
Explain what `IsMinimal` means by this definition.
Dependencies : accessible-fin-dfa, dfa-hom
-/

namespace DFA

universe u v w

variable {α : Type u} {σ₁ : Type v} {σ₂ : Type w}

/-- A morphism of DFAs from `M` to `N`. -/
structure Hom (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- Underlying function map from states of `M` to states of `N`. -/
  toFun : σ₁ → σ₂
  /-- The function preserves the start state. -/
  map_start : toFun M.start = N.start
  /-- The function preserves the set of accepting states. -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ toFun q ∈ N.accept
  /-- The function preserves state transitions. -/
  map_step (q : σ₁) (w : List α) : toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

/-- `M →ₗ N` denotes the type of `DFA.Hom M N`. -/
infixr:25 " →ₗ " => Hom

variable {M : DFA α σ₁} {N : DFA α σ₂}

/-- A morphism of DFAs preserves the accepted language. -/
theorem Hom.pres_lang (f : M →ₗ N) : M.accepts = N.accepts := by
  ext w
  simp_all [mem_accepts, eval]
  constructor
  · intro h
    rw [f.map_accept] at h
    rw [f.map_step M.start w] at h
    rw [f.map_start] at h
    exact h
  · intro h
    rw [f.map_accept]
    rw [f.map_step M.start w]
    rw [f.map_start]
    exact h

/-- The identity morphism on a DFA. -/
def Hom.refl (M : DFA α σ₁) : M →ₗ M where
  toFun := id
  map_start := by rfl
  map_accept := by intro q; simp
  map_step := by intro q w; simp

/-- An equivalence of DFAs is a bijective morphism. -/
structure Equiv (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- The forward morphism. -/
  toDFAHom : M →ₗ N
  /-- The reverse morphism. -/
  toInvDFAHom : N →ₗ M
  /-- Left inverse property. -/
  left_inv : Function.LeftInverse toInvDFAHom.toFun toDFAHom.toFun
  /-- Right inverse property. -/
  right_inv : Function.RightInverse toInvDFAHom.toFun toDFAHom.toFun

/-- `M ≃ₗ N` denotes the type of `DFA.Equiv M N`. -/
infixr:25 " ≃ₗ " => Equiv

/-- The identity equivalence on a DFA. -/
def Equiv.refl (M : DFA α σ₁) : M ≃ₗ M where
  toDFAHom := Hom.refl M
  toInvDFAHom := Hom.refl M
  left_inv := by tauto
  right_inv := by tauto

end DFA

/-! ### Surjective Morphisms of AccessibleFinDFAs -/

namespace AccessibleFinDFA

universe u v w

variable {α : Type u}
variable {σ₁ : Type v}
variable {σ₂ : Type w}

/-- A surjective morphism between the underlying DFAs of `AccessibleFinDFA`s. -/
structure HomSurj (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂)
    extends f : (M : DFA α σ₁) →ₗ (N : DFA α σ₂) where
  /-- The function is surjective. -/
  surjective : Function.Surjective f.toFun

/-- `M ↠ N` denotes the type of `AccessibleFinDFA.HomSurj M N`. -/
infixr:25 " ↠ " => HomSurj

/-- Forget the surjectivity proof and view `HomSurj` as a DFA morphism. -/
@[simp] def HomSurj.toDFAHom {M : AccessibleFinDFA α σ₁} {N : AccessibleFinDFA α σ₂}
  (f : M ↠ N) : (M : DFA α σ₁) →ₗ (N : DFA α σ₂) where
  toFun := f.toFun
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

/-! ### Partial Order on AccessibleFinDFAs -/

/-- The preorder on `AccessibleFinDFA`s: `M ≤ N` iff there is a surjective morphism `N ↠ M`. -/
def le (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂) : Prop :=
  Nonempty (N ↠ M)

/-- `M ≤ N` denotes the proposition `le M N`. -/
infix:25 " ≤ " => le

/-- Reflexivity of the preorder on `AccessibleFinDFA`s. -/
lemma le_refl (M : AccessibleFinDFA α σ₁) : M ≤ M := by
  simp [le]
  refine ⟨?f⟩
  refine AccessibleFinDFA.HomSurj.mk (DFA.Hom.refl M.toDFA) ?_
  intro s
  exact ⟨s, rfl⟩

/-- Transitivity of the preorder on `AccessibleFinDFA`s. -/
lemma le_trans {σ₃ : Type*} {M : AccessibleFinDFA α σ₁} {N : AccessibleFinDFA α σ₂}
  {O : AccessibleFinDFA α σ₃} (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
  obtain f := h₁.some
  obtain g := h₂.some
  refine ⟨?_⟩
  -- Compose the underlying DFA morphisms and show surjectivity.
  let I : O.toDFA →ₗ M.toDFA := by
    refine DFA.Hom.mk
      (toFun := f.toFun ∘ g.toFun)
      (map_start := by
        simp
        have hg := g.map_start
        have hf := f.map_start
        simp_all)
      (map_accept := by
        intro q
        simp_all
        have hg := g.map_accept q
        have hf := f.map_accept (g.toFun q)
        simp_all)
      (map_step := by
        intro q w
        simp_all
        have hg := g.map_step q w
        have hf := f.map_step (g.toFun q) w
        simp_all)
  refine AccessibleFinDFA.HomSurj.mk I ?_
  -- Surjectivity of the composition.
  have hI : I.toFun = f.toFun ∘ g.toFun := rfl
  simpa [hI] using Function.Surjective.comp f.surjective g.surjective

/-- Antisymmetry of the preorder up to equivalence of the underlying DFAs. -/
lemma le_antisymm (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂)
    (h₁ : M ≤ N) (h₂ : N ≤ M) :
    Nonempty ((M : DFA α σ₁) ≃ₗ (N : DFA α σ₂)) := by
  obtain f := h₁.some
  obtain g := h₂.some
  refine ⟨?_⟩
  refine DFA.Equiv.mk
    (toDFAHom := g.toDFAHom)
    (toInvDFAHom := f.toDFAHom)
    (left_inv := by
      -- Use accessibility to move back to the start state, then cancel via maps.
      simp_all [Function.LeftInverse]
      intro s
      obtain ⟨w, hs⟩ := M.is_accessible s
      rw [← hs]
      have hg₁ := g.map_step M.start w
      have hf₁ := f.map_step (g.toFun M.start) w
      have hg₂ := g.map_start
      have hf₂ := f.map_start
      rw [← hg₁] at hf₁
      simp_all)
    (right_inv := by
      simp_all [Function.RightInverse]
      intro s
      obtain ⟨w, hs⟩ := N.is_accessible s
      rw [← hs]
      have hg₁ := g.map_step M.start w
      have hf₁ := f.map_step (g.toFun M.start) w
      have hg₂ := g.map_start
      have hf₂ := f.map_start
      rw [← hg₁] at hf₁
      simp_all)

set_option linter.unusedVariables false in
/-- An `AccessibleFinDFA` is minimal if every smaller DFA is equivalent to it. -/
def IsMinimal (M : AccessibleFinDFA α σ₁) : Prop :=
  ∀ {σ₂ : Type*} [Fintype σ₂] [DecidableEq σ₂] (N : AccessibleFinDFA α σ₂) (hle : N ≤ M),
    Nonempty ((M : DFA α σ₁) ≃ₗ (N : DFA α σ₂))

end AccessibleFinDFA
