import MyProject.DFA.Accessible

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

## Implementation Notes

Note that the partial order on Accessible DFAs is not given a `LE` instance on any type,
becuase the partial order is defined on all Accessible DFAs with the same alphabet type, but they
can have different state types. Thus, there is no single type of Accessible DFAs to
put the `LE` instance on.

## TODO

Prove that equivalence is symmetric and transitive
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

lemma Hom.pres_acceptsFrom {M : DFA α σ₁} {N : DFA α σ₂} (f : M →ₗ N) (s : σ₁) :
    M.acceptsFrom s = N.acceptsFrom (f.toFun s) := by
  ext w
  simp_all [mem_acceptsFrom]
  rw [← f.map_step, f.map_accept]

/-- A morphism of DFAs preserves the accepted language. -/
theorem Hom.pres_lang {M : DFA α σ₁} {N : DFA α σ₂} (f : M →ₗ N) : M.accepts = N.accepts := by
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

/-- Regesters a injective coersion from morphisms `M →ₗ N` to functions from the state type of M
to the state type of N. -/
instance {M : DFA α σ₁} {N : DFA α σ₂} : CoeFun (M →ₗ N) fun _ ↦ (σ₁ → σ₂) where
  coe f := f.toFun

/-- An equivalence of DFAs is a bijective morphism. -/
structure Equiv (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- The bijection between the state spaces -/
  statesEquiv : σ₁ ≃ σ₂
  /-- The equivalence preserves the start state. -/
  map_start : statesEquiv M.start = N.start
  /-- The equivalence preserves the set of accepting states. -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ statesEquiv q ∈ N.accept
  /-- The equivalence preserves state transitions. -/
  map_step (q : σ₁) (w : List α) : statesEquiv (M.evalFrom q w) = N.evalFrom (statesEquiv q) w

/-- `M ≃ₗ N` denotes the type of `DFA.Equiv M N`. -/
infixr:25 " ≃ₗ " => Equiv

/-- The identity equivalence on a DFA. -/
def equivRefl (M : DFA α σ₁) : M ≃ₗ M where
  statesEquiv := Equiv.refl σ₁
  map_start := by rfl
  map_accept := by simp
  map_step := by simp

/-! ### Surjective Morphisms of AccessibleFinDFAs -/

/-- A structure extending `DFA.Hom` asserting that the morphism is surjective -/
structure HomSurj (M : DFA α σ₁) (N : DFA α σ₂)
    extends f : M →ₗ (N : DFA α σ₂) where
  /-- The function is surjective. -/
  surjective : Function.Surjective f

/-- `M ↠ N` denotes the type of `DFA.HomSurj M N`. -/
infixr:25 " ↠ " => HomSurj

/-- Regesters a injective coersion from morphisms `M ↠ N` to functions from the state type of M
to the state type of N. -/
instance {M : DFA α σ₁} {N : DFA α σ₂} : CoeFun (M ↠ N) fun _ ↦ (σ₁ → σ₂) where
  coe f := f.toFun

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
  statesEquiv := by
    refine _root_.Equiv.mk (f.toFun) (f.toFun.surjInv f.surjective) ?_ ?_
    · have hbij : f.toFun.Bijective := by simp_all [f.surjective, Function.Bijective]
      exact Function.leftInverse_surjInv hbij
    · exact Function.rightInverse_surjInv f.surjective
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

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
      (toFun := f ∘ g)
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
        have hf := f.map_step (g q) w
        simp_all)
  refine HomSurj.mk I ?_
  -- Surjectivity of the composition.
  have hI : I.toFun = f ∘ g := rfl
  simpa [hI] using Function.Surjective.comp f.surjective g.surjective

variable {M : DFA α σ₁} [Accessible M] {N : DFA α σ₂} [Accessible N]
in
/-- Antisymmetry of the preorder up to equivalence of DFAs. -/
lemma accessibleLE_antisymm (h₁ : M ≤ N) (h₂ : N ≤ M) : Nonempty (M ≃ₗ N) := by
  obtain f := h₁.some
  obtain g := h₂.some
  refine ⟨?_⟩
  let equiv : σ₁ ≃ σ₂ := by
    refine _root_.Equiv.mk (g.toFun) (f.toFun) ?_ ?_
    · intros s
      have hsplit := M.accessible_split s
      rcases hsplit with (hs | ⟨w, hw, hs⟩)
      · subst hs
        simp [g.map_start, f.map_start]
      · subst hs
        simp_all [eval, g.map_step, f.map_step, g.map_start, f.map_start]
    · intros s
      have hsplit := N.accessible_split s
      rcases hsplit with (hs | ⟨w, hw, hs⟩)
      · subst hs
        simp [g.map_start, f.map_start]
      · subst hs
        simp_all [eval, g.map_step, f.map_step, g.map_start, f.map_start]
  refine Equiv.mk equiv ?_ ?_ ?_
  · unfold equiv
    simp [g.map_start]
  · unfold equiv
    simp [g.map_accept]
  · unfold equiv
    simp [g.map_step]

/-- An accessible DFA is minimal if every smaller accessible DFA is equivalent to it. -/
def IsMinimal (M : DFA α σ₁) [Accessible M] : Prop :=
  ∀ {σ₂ : Type*} (N : DFA α σ₂) [Accessible N] (_ : N ≤ M),
    Nonempty (M ≃ₗ N)

end DFA
