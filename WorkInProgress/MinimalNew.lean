import MyProject.New.NerodeNew
import MyProject.New.HomNew
import Mathlib

namespace DFA

universe u v

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-- The language of words `w` such that `M.evalFrom (M.step s a) w ∈ M.accept`
is equal to the left quotient of `M.acceptsFrom s` by `[a]` -/
lemma acceptsFrom_step (s : σ) (a : α) :
    M.acceptsFrom (M.step s a) = (M.acceptsFrom s).leftQuotient [a] := by
  ext w
  have heq : ∀ w, a :: w = [a] ++ w := fun w ↦ rfl
  simp [Language.leftQuotient, mem_acceptsFrom]
  conv=> rhs; lhs; rhs; ext y; rw [(heq y)]
  simp only [evalFrom_of_append, evalFrom_singleton]
  rfl

/-- If s₁, s₂ are Nerode Equivilant, then so are
`M.step s₁ a` and `M.step s₂ a` for all `a : α` -/
lemma nerode_step {s₁ s₂ : σ} (h : M.Nerode s₁ s₂) (a : α) :
    M.Nerode (M.step s₁ a) (M.step s₂ a) := by
  simp_all [Nerode, acceptsFrom_step]

/-- For a DFA `M`, `M.toNerodeDFA` is a DFA whose state-space is the
quotient of `M`'s by the nerode Equivalence. This is the minimum
DFA, assuming that `M` is accessible. -/
def toNerodeDFA :
    DFA α (Quotient (M.Nerode)) where
  step (s' : Quotient (M.Nerode)) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerode_step; apply h) s'
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
  exact List.foldl_hom (init := s) (l := w) (Quotient.mk M.Nerode)
    (fun (s₁ : σ) (a : α) ↦ M.toNerodeDFA_step_def s₁ a)

@[simp] lemma toNerodeDFA_eval_def (w : List α) :
    M.toNerodeDFA.eval w = ⟦M.eval w⟧ := by simp [DFA.eval]

/-- If s₁ and s₂ are Nerode equivalent, then s₁ is an accepting state
iff s₂ is an accepting state. -/
lemma nerode_pres_mem_accept {s₁ s₂ : σ} (hn : M.Nerode s₁ s₂) :
    s₁ ∈ M.accept ↔ s₂ ∈ M.accept := by
  simp_all [Nerode, acceptsFrom]
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

/-- If M is accessible, then so is M.toNerodeDFA. -/
instance toNerodeDFA_pres_accessible (M : DFA α σ) [Accessible M] :
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
instance toNerodeDFA_pres_fin (M : DFA α σ) [hf : Fin M] : Fin M.toNerodeDFA where
  finAccept := {⟦q⟧ | q ∈ hf.finAccept}
  accept_eq := by simp_all

/-- Two states are nerode equivalent iff the words accessing them induce
the same left quotient on `M.accepts`. -/
lemma nerode_iff_leftQuotient_eq {s₁ s₂ : σ} {w₁ w₂ : List α}
  (hs₁ : M.eval w₁ = s₁) (hs₂ : M.eval w₂ = s₂) :
    M.Nerode s₁ s₂ ↔ M.accepts.leftQuotient w₁ = M.accepts.leftQuotient w₂ := by
  simp [Nerode, Language.leftQuotient_accepts_apply, ← hs₁, ← hs₂]


/-- M.toNerodeDFA is equivlaent to the DFA obtained by using `Language.toDFA` on
`M.accepts` (where states are left quotients of the language). -/
def toNerodeDFA_eq_accepts_toDFA [Accessible M] : M.accepts.toDFA ≃ₗ M.toNerodeDFA where
  toDFAHom :=
    { toFun (x : ↑(Set.range M.accepts.leftQuotient)) := by
        obtain ⟨x, hx⟩ := x
        simp_all
        use ⟦M.eval hx.choose⟧
      map_start := by
        simp_all
        have h := (id (Eq.refl fun y ↦ M.accepts.leftQuotient y = M.accepts) ▸ Eq.mp Set.mem_range._simp_1 M.accepts.toDFA.2.property ).choose_spec
        simp_all [Nerode, Language.leftQuotient_accepts]
        simp [accepts]
      map_accept := by
        intro l
        have h := (id (Eq.refl fun y ↦ M.accepts.leftQuotient y = M.accepts) ▸ Eq.mp Set.mem_range._simp_1 M.accepts.toDFA.2.property ).choose_spec
        simp_all [Language.leftQuotient_accepts]
        sorry
      map_step := _ }

  toInvDFAHom :=
    { toFun (x : Quotient M.Nerode) := by
        use M.toNerodeDFA.acceptsFrom x
        simp [Language.leftQuotient_accepts]
        obtain ⟨s, hs⟩ := Quotient.exists_rep x
        subst hs
        simp
        obtain ⟨w, hw⟩ := M.allAccessible s
        use w; rw [hw]
      map_start := by
        apply Subtype.eq
        simp [accepts]
      map_accept (q : Quotient M.Nerode) := by
        simp
        obtain ⟨s, hs⟩ := Quotient.exists_rep q
        subst hs
        simp [Nerode]
        constructor
        ·

      map_step := _ }
  left_inv := by sorry
  right_inv := by sorry

/-- The cannonical surjective morphism from a DFA to its nerode DFA induced by
`Quotient.mk M.Nerode` -/
def toNerodeDFA_homSurj (M : DFA α σ) : M ↠ M.toNerodeDFA where
  toFun := Quotient.mk M.Nerode
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

/-- The Nerode automaton is ≤ the original automaton in the partial order. -/
lemma toNerodeDFA_le (M : DFA α σ) [Accessible M] : M.toNerodeDFA ≤ M := by
  apply Nonempty.intro
  exact M.toNerodeDFA_homSurj

lemma toNerodeDFA_eq_of_nerode (M : DFA α σ) {s₁ s₂ : Quotient M.Nerode}
  (hn : M.toNerodeDFA.Nerode s₁ s₂) : s₁ = s₂ := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep s₁
  obtain ⟨b, hb⟩ := Quotient.exists_rep s₂
  subst hb ha
  have h := M.toNerodeDFA_acceptsFrom_def a
  have h := M.toNerodeDFA_acceptsFrom_def b
  simp_all [Nerode]

variable {σ₂ : Type*} (M : DFA α σ) (N : DFA α σ₂) in
lemma Hom.pres_nerode (s₁ s₂ : σ) (f : M →ₗ N) :
    M.Nerode s₁ s₂ ↔ N.Nerode (f.toFun s₁) (f.toFun s₂) := by
  simp [Nerode, f.pres_acceptsFrom]

/-- The nerode automaton is minimal in the partial order on accessible DFAs -/
theorem nerodeAutomaton_isMinimal (M : DFA α σ) [Accessible M] :
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
  simp_all [Nerode]

end DFA
