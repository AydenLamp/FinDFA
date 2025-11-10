import MyProject.New.Accessible

/-!
# Morphisms between DFAs

This file defines morphisms between DFAs, which are bundled functions between the state spaces
that respect the transition function, start state, and accept states of the DFAs.

We then define a partial order on Accessible DFAs where `M ≤ N` iff there exists a surjective
morphism from `N.toDFA` to `M.toDFA`.

## Main definitions

* `DFA.Hom` - A morphism from the `DFA` `M` to the `DFA` `N`, notated `M →ₗ N`.

* `DFA.Equiv` - An equivalence of `DFA`s, which is a bijective morphism, notated `M ≃ₗ N`.

* `DFA.HomSurj` - A surjective DFA morphism. Notated `M ↠ N`.

* `DFA.AccessibleLE` - Notated `≤`, the partial order on Accessible DFAs.

* `DFA.AccessibleIsMinimal` - A predicate that `M` is minimal by the partial order, up to
  equivalence of `DFA`s.

## Main theorems

* `DFA.Hom.pres_lang` - `M.accepts = N.accepts` when there exists `f : M →ₗ N`.

* `DFA.accessibleLE_refl` - Reflexivity of `≤`.

* `DFA.accessibleLE_trans` - Transitivity of `≤`.

* `DFA.accessibleLE_antisymm` - Antisymmetry of `≤` up to equivalence of underlying DFAs.

## Notation

* `M →ₗ N` - Notation for `DFA.Hom M N`.

* `M ≃ₗ N` - Notation for `DFA.Equiv M N`.

* `M ↠ N` - Notation for `DFA.HomSurj M N`.

* `M ≤ N` - Notation for the partial order on Accessible DFAs.
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

lemma Hom.pres_acceptsFrom (f : M →ₗ N) (s : σ₁) :
    M.acceptsFrom s = N.acceptsFrom (f.toFun s) := by
  ext w
  simp_all [mem_acceptsFrom]
  rw [← f.map_step, f.map_accept]

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
def homRefl (M : DFA α σ₁) : M →ₗ M where
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
def equivRefl (M : DFA α σ₁) : M ≃ₗ M where
  toDFAHom := M.homRefl
  toInvDFAHom := M.homRefl
  left_inv := by tauto
  right_inv := by tauto

/-! ### Surjective Morphisms of AccessibleFinDFAs -/

/-- A structure extending `DFA.Hom` asserting that the morphism is surjective -/
structure HomSurj (M : DFA α σ₁) (N : DFA α σ₂)
    extends f : M →ₗ (N : DFA α σ₂) where
  /-- The function is surjective. -/
  surjective : Function.Surjective f.toFun

/-- `M ↠ N` denotes the type of `DFA.HomSurj M N`. -/
infixr:25 " ↠ " => HomSurj

variable {M : DFA α σ₁} {N : DFA α σ₂}
in
/-- Forget the surjectivity proof and view `HomSurj` as a DFA morphism. -/
@[simp] def HomSurj.toDFAHom (f : M ↠ N) : M →ₗ N where
  toFun := f.toFun
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

variable {M : DFA α σ₁} {N : DFA α σ₂}
in
/-- Lift a `HomSurj` that is also injective into an `Equiv` by using the
noncomputable inverse function `f.toFun.surjInv f.surjective` -/
noncomputable def HomSurj.equiv_of_inj (f : M ↠ N) (hf : f.toFun.Injective) : M ≃ₗ N where
  toDFAHom := f.toDFAHom
  toInvDFAHom := {
    toFun (s : σ₂) := f.toFun.surjInv f.surjective s
    map_start := by
      have hbij : f.toFun.Bijective := by simp_all [f.surjective, Function.Bijective]
      have hid : ((f.toFun.surjInv f.surjective) ∘ f.toFun) = id := by
        rw [← Function.leftInverse_iff_comp]
        exact Function.leftInverse_surjInv hbij
      have hf : f.toFun M.start = N.start := by
        apply f.map_start
      rw [← hf]
      have heq : Function.surjInv f.surjective (f.toFun M.start) =
        (Function.surjInv f.surjective ∘ f.toFun) M.start := by rfl
      rw [heq, hid]
      simp
    map_accept (s : σ₂):= by
      have hf' := f.map_accept (Function.surjInv f.surjective s)
      rw [hf']
      have hid : (f.toFun ∘ (f.toFun.surjInv f.surjective)) = id := by
        rw [← Function.rightInverse_iff_comp]
        exact Function.rightInverse_surjInv f.surjective
      have heq : f.toFun (Function.surjInv f.surjective s) =
        (f.toFun ∘ (Function.surjInv f.surjective)) s := by rfl
      rw [heq, hid]
      simp
    map_step (s : σ₂) (w : List α) := by
      have hf' := f.map_step (Function.surjInv f.surjective s) w
      have hid : (f.toFun ∘ (f.toFun.surjInv f.surjective)) = id := by
        rw [← Function.rightInverse_iff_comp]
        exact Function.rightInverse_surjInv f.surjective
      have heq : f.toFun (Function.surjInv f.surjective s) =
        (f.toFun ∘ (Function.surjInv f.surjective)) s := by rfl
      rw [heq, hid] at hf'
      simp at hf'
      rw [← hf']
      have hbij : f.toFun.Bijective := by simp_all [f.surjective, Function.Bijective]
      have hid' : ((f.toFun.surjInv f.surjective) ∘ f.toFun) = id := by
        rw [← Function.leftInverse_iff_comp]
        exact Function.leftInverse_surjInv hbij
      have heq' :
        Function.surjInv f.surjective (f.toFun
          (M.evalFrom (Function.surjInv f.surjective s) w)) =
        (Function.surjInv f.surjective ∘ f.toFun)
          (M.evalFrom (Function.surjInv f.surjective s) w) := by rfl
      rw [heq', hid']
      simp }
  left_inv := by
    have hbij : f.toFun.Bijective := by simp_all [f.surjective, Function.Bijective]
    exact Function.leftInverse_surjInv hbij
  right_inv := Function.rightInverse_surjInv f.surjective

/-! ### Partial Order on Accessible DFAs -/

/-- `M ≤ N` iff there is a surjective morphism `N ↠ M`. -/
def AccessibleLE (M : DFA α σ₁) [Accessible M] (N : DFA α σ₂) [Accessible N] : Prop :=
  Nonempty (N ↠ M)

/-- `M ≤ N` denotes the proposition `M.AccessibleLE M N`. -/
infix:25 " ≤ " => AccessibleLE

/-- Reflexivity of the preorder on accessible DFAs. -/
lemma accessibleLE_refl (M : DFA α σ₁) [Accessible M] : M ≤ M := by
  simp [AccessibleLE]
  refine ⟨?f⟩
  refine HomSurj.mk (M.homRefl) ?_
  intro s
  exact ⟨s, rfl⟩

variable {M : DFA α σ₁} [Accessible M] {N : DFA α σ₂} [Accessible N]
  {σ₃ : Type*} {O : DFA α σ₃} [Accessible O]
in
/-- Transitivity of the preorder on accessible DFAs. -/
lemma accessibleLE_trans (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
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
/-- Antisymmetry of the preorder up to equivalence of DFAs. -/
lemma accessibleLE_antisymm (h₁ : M ≤ N) (h₂ : N ≤ M) : Nonempty (M ≃ₗ N) := by
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

/-- An accessible DFA is minimal if every smaller accessible DFA is equivalent to it. -/
def IsMinimal (M : DFA α σ₁) [Accessible M] : Prop :=
  ∀ {σ₂ : Type*} (N : DFA α σ₂) [Accessible N] (_ : N ≤ M),
    Nonempty (M ≃ₗ N)

end DFA
