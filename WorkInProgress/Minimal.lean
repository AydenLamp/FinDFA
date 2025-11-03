import MyProject.Hom
import MyProject.Nerode
import Mathlib

/-!
# The (minimal) Nerode Automaton

We construct the *Nerode Automaton* of a given `M : AccessibleFinDFA`, which is another
`AccessibleFinDFA` defined on the state space given by the quotient of the `nerode` equivalence
relation on `M`'s states, with the transition function induced by `M`'s transition function.

We then show that this automaton accepts the same language as `M`, and that it is minimal by the
surjective-morphism based preorder on `AccessibleFinDFA`s.

## Main Definitions

* `AccessibleFinDFA.nerodeAutomaton` : A function that inputs an `M : AccessibleFinDFA` and outputs
the Nerode automaton of the language defined by `M`.

## Main Theorems

* `AccessibleFinDFA.nerodeAutomaton_pres_lang` :
  `M` and `M.nerodeAutomaton` accept the same language.

* `AccessibleFinDFA.nerodeAutomaton_isMinimal` : `M.nerodeAutomaton` is minimal by the
surjective-morphism based preorder on `AccessibleFinDFA`s. In other words, For any other
`N : AccessableFinDFA` that accepts the same language as
 `M.nerodeAutomaton`, there exists a surjective
morphism from `N.DFA` to `M.nerodeAutomaton.toDFA`.

* `AccessibleFinDFA.nerodeAutomaton_minimal_states` :
 `M.nerodeAutomaton` has the minimal number
of states among all `AccessibleFinDFA`s that accept the same language.

# TODO

Prove uniqueness of minimal automaton for all automata accepting the same language.

## Blueprint

TODO
-/

namespace AccessibleFinDFA

universe u v

variable {α : Type u} {σ : Type v}

section Finite

/-- A word indistinguishes two states iff it indistinguishes their transitions under any letter. -/
lemma nerode_step (M : AccessibleFinDFA α σ) {s₁ s₂ : σ} (h : M.nerode s₁ s₂) (a : α) :
    M.nerode (M.step s₁ a) (M.step s₂ a) := by
  simp_all [nerode, Indist]
  intros w
  specialize h (a :: w)
  simp_all [DFA.evalFrom]

variable [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]

/-- The Nerode automaton of the `AccessibleFinDFA` `M`. -/
def nerodeAutomaton (M : AccessibleFinDFA α σ) :
    AccessibleFinDFA α (Quotient (M.nerode)) where
  step (s' : Quotient (M.nerode)) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerode_step; apply h) s'
  start := ⟦M.start⟧
  accept := {⟦q⟧ | q ∈ M.accept }
  is_accessible := by
    have hacc := M.is_accessible
    simp_all [FinDFA.IsAccessibleState]
    apply Quotient.ind
    intro s
    specialize hacc s
    rcases hacc with ⟨w, hw⟩
    use w
    simp [DFA.evalFrom] at hw ⊢
    subst hw
    exact List.foldl_hom (Quotient.mk M.nerode) fun x ↦ congrFun rfl

def nerodeAutomaton_hom (M : AccessibleFinDFA α σ) :
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
          have heq' : (M.nerodeAutomaton.toDFA.evalFrom ⟦s⟧ [a]) = ⟦M.toDFA.evalFrom s [a]⟧ := by
            simp [nerodeAutomaton]
          rw [heq']
          specialize ih (M.toDFA.evalFrom s [a])
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
theorem nerodeAutomaton_pres_lang (M : AccessibleFinDFA α σ) :
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
