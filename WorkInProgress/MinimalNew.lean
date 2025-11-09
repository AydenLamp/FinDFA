import MyProject.New.NerodeNew
import MyProject.New.HomNew
import Mathlib

namespace DFA

universe u v

variable {α : Type u} {σ : Type v} (M : DFA α σ)

section Finite

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
quotient of `M`'s by the nerode Equivalence. -/
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

/-- Two states are nerode equivalent iff the words accessing them induce
the same left quotient on `M.accepts`. -/
lemma nerode_iff_leftQuotient_eq {s₁ s₂ : σ} {w₁ w₂ : List α}
  (hs₁ : M.eval w₁ = s₁) (hs₂ : M.eval w₂ = s₂) :
    M.Nerode s₁ s₂ ↔ M.accepts.leftQuotient w₁ = M.accepts.leftQuotient w₂ := by
  simp [Nerode, Language.leftQuotient_accepts_apply, ← hs₁, ← hs₂]

def toNerodeDFA_eq_accepts_toDFA [Accessible M] : M.accepts.toDFA ≃ₗ M.toNerodeDFA where
  toDFAHom := { toFun (x : ↑(Set.range M.accepts.leftQuotient)) := by
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



                map_step := _ }
  toInvDFAHom := { toFun (x : Quotient M.Nerode) := by
                     use M.toNerodeDFA.acceptsFrom x
                     simp [Language.leftQuotient_accepts]
                     obtain ⟨s, hs⟩ := Quotient.exists_rep x
                     subst hs
                     simp
                     obtain ⟨w, hw⟩ := M.allAccessible s
                     use w; rw [hw]
                   map_start := _
                   map_accept := _
                   map_step := _ }
  left_inv := by sorry
  right_inv := by sorry

instance nerodeAutomaton_pres_accessible (M : DFA α σ) [Accessible M] : Accessible M.nerodeAutomaton where
  allAccessible := by
    have hacc := M.allAccessible
    simp_all [IsAccessibleState]
    apply Quotient.ind
    intro s
    specialize hacc s
    rcases hacc with ⟨w, hw⟩
    use w
    simp
    rw [hw]

instance nerodeAutomaton_pres_fin (M : DFA α σ) [hf : Fin M] : Fin M.nerodeAutomaton where
  finAccept := {⟦q⟧ | q ∈ hf.finAccept}
  map_accept := by simp_all

def nerodeAutomaton_of_lang (L : Language α) : DFA α (Set.range L.leftQuotient) where
  step s a := by
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [← hy, Language.leftQuotient_append]
  start := ⟨L, by exists []⟩
  accept := { s | [] ∈ s.val }

lemma nerodeAutomaton_equiv_nerodeAutomaton_of_lang (M : DFA α σ) [Accessible M] :
    M.nerodeAutomaton ≃ₗ M.accepts.toDFA := by
  refine DFA.Equiv.mk ?_ ?_ ?_ ?_
  · refine DFA.Hom.mk ?_ ?_ ?_ ?_
    · intros s
      have hls : M.nerodeAutomaton.acceptsFrom s ∈ Set.range M.accepts.leftQuotient := by
        obtain ⟨w, hw⟩ := M.nerodeAutomaton.allAccessible s
        use w
        sorry
      exact ⟨M.nerodeAutomaton.acceptsFrom s, hls⟩
    · simp
      sorry
    ·








def nerodeAutomaton_hom (M : DFA α σ) [Accessible M] :
    M ↠ M.nerodeAutomaton := by
  exact
    { toFun := Quotient.mk (M.nerode)
      map_start := by simp [nerodeAutomaton]
      map_accept (s : σ) := by
        simp [nerodeAutomaton]
        constructor
        · intro h; use s
        · rintro ⟨s', hs', heq⟩
          simp_all [nerode, Indist]
          specialize heq ∅
          simp_all
      map_step (s : σ) (w : List α) := by
        induction w generalizing s with
        | nil => simp
        | cons a w ih =>
          have heq : a :: w = [a] ++ w := by simp
          simp_rw [heq, DFA.evalFrom_of_append]
          have heq' : (M.nerodeAutomaton.evalFrom ⟦s⟧ [a]) = ⟦M.evalFrom s [a]⟧ := by
            simp [nerodeAutomaton]
          rw [heq']
          specialize ih (M.evalFrom s [a])
          exact ih
      surjective := Quotient.mk_surjective }


/-- The Nerode automaton is ≤ the original automaton in the partial order. -/
lemma nerodeAutomaton_le (M : AccessibleFinDFA α σ) :
    M.nerodeAutomaton ≤ M := by
  apply Nonempty.intro
  exact
    { toFun := Quotient.mk (M.nerode)
      map_start := by simp [nerodeAutomaton]
      map_accept (s : σ) := by
        simp [nerodeAutomaton]
        constructor
        · intro h; use s
        · rintro ⟨s', hs', heq⟩
          simp_all [nerode, Indist]
          specialize heq ∅
          simp_all
      map_step (s : σ) (w : List α) := by
        induction w generalizing s with
        | nil => simp
        | cons a w ih =>
          have heq : a :: w = [a] ++ w := by simp
          simp_rw [heq, DFA.evalFrom_of_append]
          have heq' : (M.nerodeAutomaton.toDFA.evalFrom ⟦s⟧ [a]) = ⟦M.toDFA.evalFrom s [a]⟧ := by
            simp [nerodeAutomaton]
          rw [heq']
          specialize ih (M.toDFA.evalFrom s [a])
          exact ih
      surjective := Quotient.mk_surjective }

/-- `M.nerodeAutomaton` accepts the same language as `M`. -/
theorem nerodeAutomaton_pres_lang (M : DFA α σ) :
    (M.nerodeAutomaton : DFA α (Quotient (M.nerode))).accepts = (M : DFA α σ).accepts := by
  suffices h : M.nerodeAutomaton ≤ M by
    obtain ⟨h⟩ := h
    symm
    apply DFA.Hom.pres_lang
    exact h.1
  exact nerodeAutomaton_le M

end Finite

@[simp] def stateToWords (M : AccessibleFinDFA α σ) (s : σ) : Set (List α) :=
  {w | M.toDFA.evalFrom M.start w = s}


lemma nonempty_words (M : AccessibleFinDFA α σ) (s : σ) :
    Nonempty ((M.stateToWords s) : Set (List α)) := by
  have h := M.is_accessible
  specialize h s
  simp_all

noncomputable instance inhabited_words (M : AccessibleFinDFA α σ) (s : σ) :
    Inhabited (M.stateToWords s) := by
  apply Classical.inhabited_of_nonempty
  exact M.nonempty_words s

noncomputable instance inhabited_words_subtype (M : AccessibleFinDFA α σ) (s : σ) :
    Inhabited {w // M.toDFA.evalFrom M.start w = s} := by
  apply Classical.inhabited_of_nonempty
  exact M.nonempty_words s


@[simp] lemma word_correct_eval (M : AccessibleFinDFA α σ) (s : σ)
  (w : {x : List α // M.toDFA.evalFrom M.start x = s}) :
    M.toDFA.eval ↑w = s := by
  have hw := Subtype.prop w
  simp_all [DFA.eval]

@[simp] lemma word_correct_evalFrom (M : AccessibleFinDFA α σ) (s : σ)
  (w : {x : List α // M.toDFA.evalFrom M.start x = s}) :
    M.toDFA.evalFrom M.start ↑w = s := by
  have hw := Subtype.prop w
  simp_all

def stateToQuotient (M : AccessibleFinDFA α σ) (s : σ) : Language α := by
  have h := M.inhabited_words s
  obtain ⟨w, hw⟩ := h
  exact (M.toDFA.accepts.leftQuotient w)

/-- Two states are nerode equivalent iff they represent the same left quotient. -/
lemma nerode_iff_leftQuotient (M : AccessibleFinDFA α σ) (s₁ s₂ : σ) :
    M.nerode s₁ s₂ ↔ M.stateToQuotient s₁ = M.stateToQuotient s₂ := by
  simp_all [nerode, Indist, stateToQuotient, Language.leftQuotient]
  simp [DFA.mem_accepts]
  simp [DFA.eval, DFA.evalFrom_of_append]
  have h₁ := (M.word_correct_evalFrom s₁) default
  have h₂ := (M.word_correct_evalFrom s₂) default
  simp_all
  rw [Set.setOf_inj]
  rw [@funext_iff]
  simp_all


lemma Hom.pres_leftQuotient (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂) (f : M ↠ N)
  (s : σ₁) : M.stateToQuotient s = N.stateToQuotient (f.toFun s) := by
  ext w
  simp [stateToQuotient, DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append]
  have h₁ := (M.word_correct_evalFrom s) default
  have h₂ := (N.word_correct_evalFrom (f.toFun s)) default
  simp_all
  have h := f.pres_lang
  simp [DFA.accepts, DFA.acceptsFrom] at h
  rw [Set.setOf_inj] at h
  simp_all [@funext_iff]
  have h₂ := f.map_step
  specialize h₂ s w
  simp_all
  rw [← h₂]
  apply f.map_accept

variable [Fintype α] [Fintype σ] [DecidableEq α] [DecidableEq σ]

lemma nerodeAutomaton_pres_left_Quotient (M : AccessibleFinDFA α σ) (s : σ) :
    M.stateToQuotient s = M.nerodeAutomaton.stateToQuotient (⟦s⟧) := by
  let f : M ↠ M.nerodeAutomaton := M.nerodeAutomaton_hom
  have hf := Hom.pres_leftQuotient M M.nerodeAutomaton f s
  simp_all
  rfl

lemma quotient_eq_iff_nerode (M : AccessibleFinDFA α σ) : ∀ (s₁ s₂ : Quotient M.nerode),
    M.nerodeAutomaton.nerode s₁ s₂ ↔ s₁ = s₂ := by
  apply Quotient.ind₂
  intros a b
  rw [Quotient.eq]
  have h₁ := M.nerode_iff_leftQuotient a b
  have h₂ := M.nerodeAutomaton.nerode_iff_leftQuotient ⟦a⟧ ⟦b⟧
  have ha := M.nerodeAutomaton_pres_left_Quotient a
  have hb := M.nerodeAutomaton_pres_left_Quotient b
  rw [h₁, h₂, ← ha, ← hb]

lemma eq_iff_leftQuotient (M : AccessibleFinDFA α σ) : ∀ (s₁ s₂ : Quotient M.nerode),
    M.nerodeAutomaton.stateToQuotient s₁ = M.nerodeAutomaton.stateToQuotient s₂
    ↔ s₁ = s₂ := by
  apply Quotient.ind₂
  intros s₁ s₂
  have h := M.nerodeAutomaton.nerode_iff_leftQuotient ⟦s₁⟧ ⟦s₂⟧
  rw [← h]
  rw [M.quotient_eq_iff_nerode]

/-- The nerode automaton is less than all automata that accept the same language. -/
theorem nerodeAutomaton_isMinimal (M : AccessibleFinDFA α σ) :
    (M.nerodeAutomaton).IsMinimal := by
  intro σ₂ _ _ N hle
  simp [le] at hle
  rcases hle with ⟨h⟩
  apply Nonempty.intro
  let M' := M.nerodeAutomaton

  have hbij : h.toFun.Bijective := by
    refine (Function.bijective_iff_existsUnique h.toFun).mpr ?_
    intros s
    have h₁ := h.map_step

    have h₂ : ∃ a, h.toFun a = s := by
      apply h.surjective
    obtain ⟨a, ha⟩ := h₂
    refine ExistsUnique.intro a ha ?_
    intro b hb

    have h₃ := M.eq_iff_leftQuotient a b
    symm
    rewrite [← h₃]
    have ha₂ := Hom.pres_leftQuotient M.nerodeAutomaton N h a
    have hb₂ := Hom.pres_leftQuotient M.nerodeAutomaton N h b
    rw [ha₂, hb₂, ha, hb]
  let hinv := h.toFun.surjInv h.surjective
  have left_inv : Function.LeftInverse hinv h.toFun := Function.leftInverse_surjInv hbij
  have left_inv' : hinv ∘ h.toFun  = id := by
    rw [← Function.leftInverse_iff_comp]
    exact left_inv
  have right_inv : Function.RightInverse hinv h.toFun := Function.rightInverse_surjInv h.surjective
  have right_inv' : h.toFun ∘ hinv = id := by
    rw [← Function.rightInverse_iff_comp]
    exact right_inv

  have hcomp₁ (s : σ₂) : h.toFun (hinv s) = s := by
    have h : (h.toFun ∘ hinv) s = id s := by rw [right_inv']
    simp_all

  have hcomp₂ (s : Quotient (M.nerode)) : hinv (h.toFun s) = s := by
    have h : (hinv ∘ h.toFun) s = id s := by rw [left_inv']
    simp_all

  let InvDFAHom : (N : DFA α σ₂) →ₗ (M' : DFA α (Quotient (M.nerode))) :=
    { toFun := hinv
      map_start := by
        simp
        have h₁ : h.toFun (M.nerodeAutomaton.start) = N.start := by
          apply h.map_start
        rw [← h₁, hcomp₂]
      map_accept (q : σ₂) := by
        simp
        have h₁ : ∀ q', q' ∈ M'.accept ↔ (h.toFun q') ∈ N.accept := by
          apply h.map_accept
        specialize h₁ (hinv q)
        rw [h₁, hcomp₁]
      map_step (q : σ₂) (w : List α) := by
        simp_all
        have h₁ := h.map_step (hinv q) w
        rw [hcomp₁] at h₁
        simp_all
        rw [← h₁, hcomp₂] }
  exact
    { toDFAHom := h.1
      toInvDFAHom := InvDFAHom
      left_inv := left_inv
      right_inv := right_inv }

/-- Alternative definition of minimality. -/
def IsMinimalAlt (M : AccessibleFinDFA α σ) : Prop :=
  ∀ {σ₂ : Type*} [Fintype σ₂] [DecidableEq σ₂] (N : AccessibleFinDFA α σ₂),
  (N : DFA α σ₂).accepts = (M : DFA α σ).accepts → M.nerodeAutomaton ≤ N

end AccessibleFinDFA

namespace Language

structure FinRegularLanguage (α : Type*) where
  L : Language α
  leftQuotients : Finset (Language α)
  leftQuotient_mem : ∀ x : List α, L.leftQuotient x ∈ leftQuotients

namespace FinRegularLanguage

variable {α : Type*} (L : FinRegularLanguage α)
def FinRegularLanguage.toAccessibleFinDFA

end FinRegularLanguage


end Language
