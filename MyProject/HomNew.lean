import MyProject.DefsNew
import Mathlib

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

/-! ### Surjective Morphisms of AccessibleFinDFAs -/

structure HomSurj (M : DFA α σ₁) [Accessible M] (N : DFA α σ₂) [Accessible N]
    extends f : M →ₗ (N : DFA α σ₂) where
  /-- The function is surjective. -/
  surjective : Function.Surjective f.toFun

/-- `M ↠ N` denotes the type of `AccessibleFinDFA.HomSurj M N`. -/
infixr:25 " ↠ " => HomSurj

variable {M : DFA α σ₁} [Accessible M] {N : DFA α σ₂} [Accessible N]
in
/-- Forget the surjectivity proof and view `HomSurj` as a DFA morphism. -/
@[simp] def HomSurj.toDFAHom (f : M ↠ N) : M →ₗ N where
  toFun := f.toFun
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

/-! ### Partial Order on Accessible DFAs -/

/-- `M ≤ N` iff there is a surjective morphism `N ↠ M`. -/
def le (M : DFA α σ₁) [Accessible M] (N : DFA α σ₂) [Accessible N] : Prop :=
  Nonempty (N ↠ M)

/-- `M ≤ N` denotes the proposition `le M N`. -/
infix:25 " ≤ " => le

/-- Reflexivity of the preorder on `AccessibleFinDFA`s. -/
lemma le_refl (M : DFA α σ₁) [Accessible M] : M ≤ M := by
  simp [le]
  refine ⟨?f⟩
  refine HomSurj.mk (Hom.refl M) ?_
  intro s
  exact ⟨s, rfl⟩

variable {M : DFA α σ₁} [Accessible M] {N : DFA α σ₂} [Accessible N]
  {σ₃ : Type*} {O : DFA α σ₃} [Accessible O]
in
/-- Transitivity of the preorder on `AccessibleFinDFA`s. -/
lemma le_trans (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
  obtain f := h₁.some
  obtain g := h₂.some
  refine ⟨?_⟩
  -- Compose the underlying DFA morphisms and show surjectivity.
  let I : O →ₗ M := by
    refine Hom.mk
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
  refine HomSurj.mk I ?_
  -- Surjectivity of the composition.
  have hI : I.toFun = f.toFun ∘ g.toFun := rfl
  simpa [hI] using Function.Surjective.comp f.surjective g.surjective

variable {M : DFA α σ₁} [Accessible M] {N : DFA α σ₂} [Accessible N]
in
/-- Antisymmetry of the preorder up to equivalence of the underlying DFAs. -/
lemma le_antisymm (h₁ : M ≤ N) (h₂ : N ≤ M) : Nonempty (M ≃ₗ N) := by
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
      obtain ⟨w, hs⟩ := M.allAccessible s
      rw [← hs]
      have hg₁ := g.map_step M.start w
      have hf₁ := f.map_step (g.toFun M.start) w
      have hg₂ := g.map_start
      have hf₂ := f.map_start
      rw [← hg₁] at hf₁
      subst hs
      simp_all [eval])
    (right_inv := by
      simp_all [Function.RightInverse]
      intro s
      obtain ⟨w, hs⟩ := N.allAccessible s
      rw [← hs]
      have hg₁ := g.map_step M.start w
      have hf₁ := f.map_step (g.toFun M.start) w
      have hg₂ := g.map_start
      have hf₂ := f.map_start
      rw [← hg₁] at hf₁
      subst hs
      simp_all [eval])

/-- An `AccessibleFinDFA` is minimal if every smaller DFA is equivalent to it. -/
def IsMinimal (M : DFA α σ₁) [Accessible M] : Prop :=
  ∀ {σ₂ : Type*} [Fintype σ₂] [DecidableEq σ₂] (N : DFA α σ₂) [Accessible N] (_ : N ≤ M),
    Nonempty (M ≃ₗ N)

end DFA
