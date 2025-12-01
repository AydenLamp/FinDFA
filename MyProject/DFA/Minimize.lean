import MyProject.DFA.Nerode
import MyProject.DFA.Hom
import Mathlib

/-!
# Minimization of DFAs

This file provides a function `DFA.minimize` that inputs a DFA `M`, and returns another
DFA that accepts the same language and is minimal. Our definition of minimality is based
on the existance of surjective DFA morphisms and defined is in `MyProject.DFA.Hom`. This
definition of minimality is stricter than simply requiring that the DFA has the minimal amount
of states, however we also prove that `M.minimize` has the minimal amount of states for all
automaton accepting the same language.

`DFA.minimize` composes `M.toAccessible`, which restricts `M` to only the accessible states,
with `M.toNerodeDFA`, which collapses states that are Nerode equivalent (note that `M.toNerodeDFA`
is accessible only when `M` is accessible). Another funtion, `Language.toDFA` (defined in
Mathlib) constructs a DFA accepting a given language by using the left quotients of the
language as the state space. This is related to the Nerode equivalance in that two states
are nerode equivalent iff the words accessing those two states induce the same left quotitent on
`M.accepts`. Using this fact, we prove that `M.minimize` is isomorphic to `M.accepts.toDFA`.

However, `M.minimize` is more computable than `M.accepts.toDFA`, and it is proven to preserve
`Fin` instances on `M` and Fintype, DecidableEq instances on the state space and alphabet of `M`.

## Main Definitions

* `DFA.toNerodeDFA` - Inputs a DFA `M`, and outputs a DFA with the same alphabet, but the
state space defined by the quotient of `M`s state space by the nerode equivalence.

* `DFA.toNerodeDFA_pres_accessible` - If `M` is accessible, then `M.toNerodeDFA` is accessible.

* `DFA.minimize` - Inputs a DFA `M`, restricts it to only the accessible states using
`DFA.toAccessible`, then colapses equivalent states by `DFA.toNerodeDFA`, producing the
minimal DFA accepting the same language as `M`.

* `DFA.minimize_accessible` - `M.minimize` is an accessible DFA.

* `DFA.minimize_eq_accepts_toDFA` - `M.minimize` is isomorphic to `M.accepts.toDFA`.

* `DFA.minimize_pres_fin` - Given `Fin M`, we obtain `Fin M.minimize`.

* `DFA.minimize_pres_fintype` - Given `Fin M`, and given Fintype and DecidableEq instances on the
state space and alphabet of `M`, we obtain a `Fintype` instance on the state space of
`M.minimize`.

* `DFA.minimize_pres_decidableEq` - Given `Fin M`, and given Fintype and DecidableEq instances on
the state space and alphabet of `M`, we obtain a `DecidableEq` instance on the state space of
`M.minimize`.

## Main Theorems

* `DFA.minimize_pres_accepts` - The language of `M.minimize` is the same as the language of `M`.

* `DFA.minimize_isMinimal` - `M.minimize` is a minimal DFA in the partial order on accessible
DFAs defined in `MyProject.DFA.Hom`.

* `DFA.minimize_least_states` - `M.minimize` has the least number of states among all DFAs accepting
the same language as `M`.
-/

namespace DFA

universe u v

variable {α : Type u} {σ : Type v}

/-- The language of words `w` such that `M.evalFrom (M.step s a) w ∈ M.accept`
is equal to the left quotient of `M.acceptsFrom s` by `[a]` -/
lemma acceptsFrom_step (M : DFA α σ) (s : σ) (a : α) :
    M.acceptsFrom (M.step s a) = (M.acceptsFrom s).leftQuotient [a] := by
  ext w
  have heq : ∀ w, a :: w = [a] ++ w := fun w ↦ rfl
  simp [Language.leftQuotient, mem_acceptsFrom]
  conv=> rhs; lhs; rhs; ext y; rw [(heq y)]
  simp only [evalFrom_of_append, evalFrom_singleton]
  rfl

/-- If s₁, s₂ are Nerode Equivilant, then so are
`M.step s₁ a` and `M.step s₂ a` for all `a : α` -/
lemma nerodeEquiv.step {M : DFA α σ} {s₁ s₂ : σ} (h : M.nerodeEquiv s₁ s₂) (a : α) :
    M.nerodeEquiv (M.step s₁ a) (M.step s₂ a) := by
  simp_all [nerodeEquiv, acceptsFrom_step]

/-- If s₁ and s₂ are Nerode equivalent, then s₁ is an accepting state
iff s₂ is an accepting state. -/
lemma nerode_pres_mem_accept {M : DFA α σ} {s₁ s₂ : σ} (hn : M.nerodeEquiv s₁ s₂) :
    s₁ ∈ M.accept ↔ s₂ ∈ M.accept := by
  simp_all [nerodeEquiv, acceptsFrom]
  constructor
  · intros hs₁
    have hin : [] ∈ {x | M.evalFrom s₁ x ∈ M.accept} := by
      simp [hs₁]
    rw [hn] at hin
    simpa
  · intros hs₂
    have hin : [] ∈ {x | M.evalFrom s₂ x ∈ M.accept} := by
      simp [hs₂]
    rw [← hn] at hin
    simpa

variable {σ₂ : Type*} {M : DFA α σ} {N : DFA α σ₂} in
/-- Nerode Equivalence is preserved by DFA morphisms. -/
lemma Hom.pres_nerode (f : M →ₗ N) (s₁ s₂ : σ) :
    M.nerodeEquiv s₁ s₂ ↔ N.nerodeEquiv (f.toFun s₁) (f.toFun s₂) := by
  simp [nerodeEquiv, f.pres_acceptsFrom]

variable (M : DFA α σ)

/-- For a DFA `M`, `M.toNerodeDFA` is a DFA whose state-space is the
quotient of `M`'s by the nerode Equivalence. -/
def toNerodeDFA :
    DFA α (Quotient (M.nerodeEquiv)) where
  step (s' : Quotient (M.nerodeEquiv)) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerodeEquiv.step; apply h) s'
  start := ⟦M.start⟧
  accept := {⟦q⟧ | q ∈ M.accept }

@[simp] lemma toNerodeDFA_start_def :
    M.toNerodeDFA.start = ⟦M.start⟧ := rfl

@[simp] lemma toNerodeDFA_accept_def :
    M.toNerodeDFA.accept = {⟦q⟧ | q ∈ M.accept } := rfl

@[simp] lemma toNerodeDFA_step_def (s : σ) (a : α) :
    M.toNerodeDFA.step ⟦s⟧ a = ⟦M.step s a⟧ := rfl

@[simp] lemma toNerodeDFA_evalFrom_def (s : σ) (w : List α) :
    M.toNerodeDFA.evalFrom ⟦s⟧ w = ⟦M.evalFrom s w⟧ := by
  simp [evalFrom]
  exact List.foldl_hom (init := s) (l := w) (Quotient.mk M.nerodeEquiv)
    (fun (s₁ : σ) (a : α) ↦ M.toNerodeDFA_step_def s₁ a)

@[simp] lemma toNerodeDFA_eval_def (w : List α) :
    M.toNerodeDFA.eval w = ⟦M.eval w⟧ := by simp [DFA.eval]

@[simp] lemma toNerodeDFA_acceptsFrom_def (s : σ) :
    M.toNerodeDFA.acceptsFrom ⟦s⟧ = M.acceptsFrom s := by
  simp [acceptsFrom]
  ext w
  rw [Set.mem_setOf]
  rw [Set.mem_setOf]
  constructor
  · rintro ⟨s₂, ⟨hs₁, hs₂⟩⟩
    rwa [M.nerode_pres_mem_accept hs₂.symm]
  · intro hw
    use M.evalFrom s w

/-- The language accepted by `M.toNerodeDFA` is the same as that of `M`. -/
@[simp] theorem toNerodeDFA_pres_accepts : M.toNerodeDFA.accepts = M.accepts := by
  simp [accepts]

/-- If `M` is accessible, then so is `M.toNerodeDFA`. -/
instance toNerodeDFA_pres_accessible [Accessible M] :
    Accessible M.toNerodeDFA where
  allAccessible := by
    have hacc := M.allAccessible
    simp_all [IsAccessibleState]
    apply Quotient.ind
    intro s
    specialize hacc s
    rcases hacc with ⟨w, hw⟩
    use w
    simp_all

variable [Fintype σ] [DecidableEq σ] [Fintype α] [DecidableEq α] in
/-- If M is Fin, then so is M.toNerodeDFA. -/
instance toNerodeDFA_pres_fin [hf : Fin M] : Fin M.toNerodeDFA where
  finAccept := {⟦q⟧ | q ∈ hf.finAccept}
  accept_eq := by simp_all

/-- The cannonical surjective morphism from a DFA to its nerode DFA induced by
`Quotient.mk M.nerodeEquiv` -/
def toNerodeDFA_homSurj : M ↠ M.toNerodeDFA where
  toFun := Quotient.mk M.nerodeEquiv
  map_start := by simp
  map_accept (s : σ) := by
    simp
    constructor
    · intro h; use s
    · rintro ⟨s', hs', heq⟩
      have h := M.nerode_pres_mem_accept heq
      rwa [← h]
  map_step (s : σ) (w : List α) := by simp
  surjective := Quotient.mk_surjective

/-- If two states of `M.toNerodeDFA` are nerode equivalent, then they are equal. -/
lemma toNerodeDFA_eq_of_nerode {M : DFA α σ} {s₁ s₂ : Quotient M.nerodeEquiv}
  (hn : M.toNerodeDFA.nerodeEquiv s₁ s₂) : s₁ = s₂ := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep s₁
  obtain ⟨b, hb⟩ := Quotient.exists_rep s₂
  subst hb ha
  have h := M.toNerodeDFA_acceptsFrom_def a
  have h := M.toNerodeDFA_acceptsFrom_def b
  simp_all [nerodeEquiv]

/-- If `M` is accessible, then `M.toNerodeDFA` is minimal
in the partial order on accessible DFAs. -/
theorem toNerodeDFA_isMinimal [Accessible M] :
    (M.toNerodeDFA).IsMinimal := by
  intro σ₂ N _ hle
  simp [AccessibleLE] at hle
  rcases hle with ⟨h⟩
  apply Nonempty.intro
  refine h.equiv_of_inj ?_
  simp [Function.Injective]
  intros a b heq
  apply M.toNerodeDFA_eq_of_nerode
  obtain ⟨s₁, hs₁⟩ := Quotient.exists_rep a
  obtain ⟨s₂, hs₂⟩ := Quotient.exists_rep b
  subst hs₁ hs₂
  rw [h.pres_nerode]
  simp_all [nerodeEquiv]

/-- Two states are nerode equivalent iff the words accessing them induce
the same left quotient on `M.accepts`. -/
lemma nerode_iff_leftQuotient_eq {M : DFA α σ} {s₁ s₂ : σ} {w₁ w₂ : List α}
  (hs₁ : M.eval w₁ = s₁) (hs₂ : M.eval w₂ = s₂) :
    M.nerodeEquiv s₁ s₂ ↔ M.accepts.leftQuotient w₁ = M.accepts.leftQuotient w₂ := by
  simp [nerodeEquiv, Language.leftQuotient_accepts_apply, ← hs₁, ← hs₂]

lemma nerode_iff_leftQuotient_eq' {M : DFA α σ} (w₁ w₂ : List α) :
    M.nerodeEquiv (M.eval w₁) (M.eval w₂) ↔
    M.accepts.leftQuotient w₁ = M.accepts.leftQuotient w₂ := by
  simp [nerodeEquiv, Language.leftQuotient_accepts_apply]

@[simp] def range_leftQuotients_equiv_subtype :
    (Set.range M.accepts.leftQuotient) ≃
    {l : Language α // ∃ w : List α, M.accepts.leftQuotient w = l} where
  toFun (s : Set.range M.accepts.leftQuotient) := by
    obtain ⟨l, hl⟩ := s
    simp at hl
    use l
  invFun (l : {l : Language α // ∃ w : List α, M.accepts.leftQuotient w = l}) := by
    use l.val; simp

@[simp] noncomputable def leftQuotients_subtype_equiv_toNeroeDFA_states [Accessible M] :
    {l : Language α // ∃ w : List α, M.accepts.leftQuotient w = l} ≃
    (Quotient M.nerodeEquiv) where
  toFun (l : {l : Language α // ∃ w : List α, M.accepts.leftQuotient w = l}) :=
    M.toNerodeDFA.eval (l.prop.choose)
  invFun (q : Quotient (M.nerodeEquiv)) := by
    use M.toNerodeDFA.acceptsFrom q
    use M.toNerodeDFA.getAccessWord q
    rw [← M.toNerodeDFA_pres_accepts]
    rw [Language.leftQuotient_accepts_apply]
    rw [← toNerodeDFA_acceptsFrom_def]
    simp_all
  left_inv := by
    intro l
    simp [← Language.leftQuotient_accepts_apply]
    have hl := l.prop.choose_spec
    simp_all
  right_inv := by
    intro q
    simp_all
    have h (q' : Quotient M.nerodeEquiv) :
        ∃ w, M.accepts.leftQuotient w = M.toNerodeDFA.acceptsFrom q' := by
      use M.toNerodeDFA.getAccessWord q'
      rw [← M.toNerodeDFA_pres_accepts]
      rw [Language.leftQuotient_accepts_apply]
      rw [← toNerodeDFA_acceptsFrom_def]
      simp_all
    have h₁ : (∃ w, M.accepts.leftQuotient w =
      @Subtype.val (Language α)
        (fun l ↦ ∃ w, M.accepts.leftQuotient w = l)
        ((fun q ↦ ⟨M.toNerodeDFA.acceptsFrom q, h q⟩) q)) := by
      simp_all
    have h₂ := Classical.choose_spec h₁
    have h₃ : ⟦M.eval h₁.choose⟧ = q := by
      simp_all
      rw [← M.toNerodeDFA_eval_def]
      conv at h₂ => lhs; lhs; rw [← M.toNerodeDFA_pres_accepts]
      rw [Language.leftQuotient_accepts_apply, ] at h₂
      apply M.toNerodeDFA_eq_of_nerode
      exact h₂
    exact h₃

@[simp] noncomputable def range_leftQuotients_equiv_toNerodeDFA_states [Accessible M] :
    Set.range M.accepts.leftQuotient ≃ (Quotient M.nerodeEquiv) :=
  Equiv.trans M.range_leftQuotients_equiv_subtype M.leftQuotients_subtype_equiv_toNeroeDFA_states

/-- If `M` is accessible, `M.toNerodeDFA` is equivlaent to the DFA obtained by using `Language.toDFA` on
`M.accepts` (where states are left quotients of the language). -/
noncomputable def toNerodeDFA_eq_accepts_toDFA [Accessible M] : M.accepts.toDFA ≃ₗ M.toNerodeDFA where
  statesEquiv := range_leftQuotients_equiv_toNerodeDFA_states M
  map_start := by
    simp
    let h : ∃ a, (fun w ↦ M.accepts.leftQuotient w = M.accepts) a := by use []; simp
    have h₂ := h.choose_spec
    have h₃ : M.nerodeEquiv (M.eval h.choose) M.start := by
      have h₄ := M.nerode_iff_leftQuotient_eq' h.choose []
      simp at h₄
      rw [h₄]
      exact h₂
    exact h₃
  map_accept := by
    simp_all
    intros l w hl
    rw [Language.leftQuotient_accepts_apply] at hl
    constructor
    · intros hnul
      use M.eval w
      constructor
      · simp [acceptsFrom] at hl
        rw [← hl] at hnul
        rw [Set.mem_setOf] at hnul
        simpa
      · have h₁ : l ∈ Set.range M.accepts.leftQuotient := by
          use w
        have h₂ : ∃ w_1, M.accepts.leftQuotient w_1 =
            @Subtype.val (Language α) (fun l ↦ ∃ w, M.accepts.leftQuotient w = l) ⟨l, h₁⟩ := by
          use w
        have h₃ : M.nerodeEquiv (M.eval w) (M.eval h₂.choose) := by
          have hspec := h₂.choose_spec
          have h₄ := M.nerode_iff_leftQuotient_eq' w h₂.choose
          rw [h₄]
          rw [hspec]
          simp_all
        exact h₃
    · rintro ⟨s, hs_accept, heq⟩
      have h₁ : l ∈ Set.range M.accepts.leftQuotient := by
        use w
      have h₂ : ∃ w_1, M.accepts.leftQuotient w_1 =
          @Subtype.val (Language α) (fun l ↦ ∃ w, M.accepts.leftQuotient w = l) ⟨l, h₁⟩ := by
        use w
      obtain ⟨w', hw'⟩ := M.allAccessible s

      have h := M.nerode_iff_leftQuotient_eq' w' h₂.choose
      simp [hw'] at h
      rw [h] at heq
      have h₃ := h₂.choose_spec
      simp at h₃
      rw [← h₃, ← heq]
      simp [mem_accepts, hw', hs_accept]
  map_step := by
    simp_all
    intros l w₁ heq w₂
    have h₁ : l ∈ Set.range M.accepts.leftQuotient := by use w₁
    have h₂ : ∃ w, M.accepts.leftQuotient w = ↑(M.accepts.toDFA.evalFrom ⟨l, h₁⟩ w₂) :=
      @leftQuotients_subtype_equiv_toNeroeDFA_states._proof_1 α σ M
        (M.accepts.toDFA.evalFrom ⟨l, Eq.substr Set.mem_range._simp_1 (Exists.intro w₁ heq)⟩ w₂)
    have h₃ : ∃ w, M.accepts.leftQuotient w =
        @Subtype.val (Language α) (fun l ↦ ∃ w, M.accepts.leftQuotient w = l) ⟨l, h₁⟩ :=
      @leftQuotients_subtype_equiv_toNeroeDFA_states._proof_1 α σ M
        ⟨l, Eq.substr (@Set.mem_range._simp_1 (Language α) (List α) M.accepts.leftQuotient l)
          (Exists.intro w₁ heq)⟩
    have h₄ : M.nerodeEquiv (M.eval h₂.choose) (M.evalFrom (M.eval h₃.choose) w₂) := by
      have hspec := h₃.choose_spec
      have hspec₂ := h₂.choose_spec
      simp_all
      have heq₂ : M.evalFrom (M.eval h₃.choose) w₂ = M.eval (h₃.choose ++ w₂) := by
        simp [eval, evalFrom_of_append]
      have h₅ := M.nerode_iff_leftQuotient_eq' h₂.choose (h₃.choose ++ w₂)
      rw [heq₂, h₅]
      simp_all [evalFrom]


      have h₆ : (List.foldl M.accepts.toDFA.step ⟨l, h₁⟩ w₂).val = List.foldl (λ x ↦ (M.accepts.toDFA.step ⟨l, h₁⟩ x).val) := by


      simp_all [Language.leftQuotient_accepts_apply]

    exact h₄



variable {σ₂ : Type*} {N : DFA α σ₂} [Fintype σ] [DecidableEq σ] [Fintype σ₂]
  [Fintype α] [DecidableEq α] [Fin M] in
/-- If `M` is accessible, then `M.toNerodeDFA` has the least amount of states of any DFA accepting
the same language. -/
lemma toNerodeDFA_least_states [Accessible M] (hAccepts : N.accepts = M.toNerodeDFA.accepts) :
    Fintype.card (Quotient (M.nerodeEquiv)) ≤ Fintype.card σ₂ := by
  rw [← @Function.Embedding.nonempty_iff_card_le]
  -- It is sufficient to construct an embedding from the states of `M.toNerodeDFA` to `N`
  sorry

/-- The minimal DFA accepting the same language as `M` -/
@[simp] def minimize : DFA α (Quotient (M.toAccessible.nerodeEquiv)) :=
  M.toAccessible.toNerodeDFA

/-- `M.minimize` accepts the same language as `M`. -/
theorem minimize_pres_accepts : M.minimize.accepts = M.accepts := by
  simp [minimize, toAccessible_pres_accepts, toNerodeDFA_pres_accepts]

/-- `M.minimize` is an Accessible DFA. -/
instance minimize_accessible : Accessible M.minimize := by simp; infer_instance

/-- `M.minimize` is minimal by our partial order defined by the existance of surjective
DFA morphisms. -/
theorem minimize_isMinimal : M.minimize.IsMinimal := by
  exact M.toAccessible.toNerodeDFA_isMinimal

/-- `M.minimize` is equivlaent to the DFA obtained by using `Language.toDFA` on
`M.accepts` (where states are left quotients of the language). -/
noncomputable def minimize_eq_accepts_toDFA : M.accepts.toDFA ≃ₗ M.minimize := by
  have h := M.toAccessible.toNerodeDFA_eq_accepts_toDFA
  have h₂ : M.toAccessible.accepts = M.accepts := by simp
  rwa [h₂] at h

variable [Fin M] [Fintype σ] [Fintype α] [DecidableEq σ] [DecidableEq α]

/-- If `M` is Fin and has Fintype and DecidableEq instances, then `M.minimize` is Fin. -/
instance minimize_pres_Fin : Fin (M.minimize) := by
  simp; infer_instance

/-- We have a Fintype instance on the state space of `M.minimize`. -/
instance minimize_pres_fintype : Fintype (Quotient (M.toAccessible.nerodeEquiv)) := by
  infer_instance

/-- We have a DecidableEq instance on the state space of `M.minimize`. -/
instance minimize_pres_decidableEq : DecidableEq (Quotient (M.toAccessible.nerodeEquiv)) := by
  infer_instance

variable {σ₂ : Type*} {N : DFA α σ₂} [Fintype σ₂]  in
/-- `M.minimize` has the least number of states among
all DFAs accepting the same language as `M`. -/
theorem minimize_least_states (hAccepts : N.accepts = M.minimize.accepts) :
    Fintype.card (Quotient (M.toAccessible.nerodeEquiv)) ≤ Fintype.card σ₂ := by
  exact M.toAccessible.toNerodeDFA_least_states hAccepts


end DFA
