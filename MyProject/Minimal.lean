import MyProject.Hom
import MyProject.Nerode
-- import Mathlib

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

* `AccessibleFinDFA.NerodeAutomaton_isMinimal` : `M.nerodeAutomaton` is minimal by the
surjective-morphism based preorder on `AccessibleFinDFA`s. In other words, For any other
`N : AccessableFinDFA` that accepts the same language as
 `M.nerodeAutomaton`, there exists a surjective
morphism from `N.DFA` to `M.nerodeAutomaton.toDFA`.

* `AccessibleFinDFA.NerodeAutomaton_minimal_states` :
 `M.nerodeAutomaton` has the minimal number
of states among all `AccessibleFinDFA`s that accept the same language.

# TODO

Prove uniqueness of minimal automaton for all automata accepting the same language.

## Blueprint

TODO


namespace AccessibleFinDFA

universe u v

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]

lemma nerode_step (M : AccessibleFinDFA α σ) {s₁ s₂ : σ} (h : M.nerode s₁ s₂) (a : α) :
    M.nerode (M.step s₁ a) (M.step s₂ a) := by
  simp_all [nerode, Indist]
  intros w
  specialize h (a :: w)
  simp_all [DFA.evalFrom]

/-- The Nerode automaton of the `AccessibleFinDFA` `M`. -/
def nerodeAutomaton (M : AccessibleFinDFA α σ) : AccessibleFinDFA α (Quotient (M.nerode)) where
  step (s' : Quotient (M.nerode)) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerode_step; apply h) s'
  start := ⟦M.start⟧
  accept := {⟦q⟧ | q ∈ M.accept }
  is_accessible := by
    have hacc := M.is_accessible
    simp_all [FinDFA.isAccessibleState]
    apply Quotient.ind
    intro s
    specialize hacc s
    rcases hacc with ⟨w, hw⟩
    use w
    simp [DFA.evalFrom] at hw ⊢
    subst hw
    exact List.foldl_hom (Quotient.mk M.nerode) fun x ↦ congrFun rfl


#check DFA

/- The *left quotient* of `x` is the set of suffixes `y` such that `x ++ y` is in `L`. -/
#check Language.leftQuotient

/-- Given a state of an `AccessibleFinDFA`, return the word reaching that state-/
def stateToWord (M : AccessibleFinDFA α σ) (s : σ) : List α := sorry

def stateToWord_correct (M : AccessibleFinDFA α σ) (s : σ) :
(M : DFA α σ).eval (M.stateToWord s) = s := by sorry

/-- Given a state of an `AccessibleFinDFA`,
return the corrosponding left quotient of the language -/
def stateToQuotient (M : AccessibleFinDFA α σ) (s : σ) : Language α :=
  ((M : DFA α σ).accepts).leftQuotient (M.stateToWord s)

/-- Two states are nerode equivilant iff they represent the same left quotient -/
lemma nerode_iff_leftQuotient (M : AccessibleFinDFA α σ) {s₁ s₂ : σ} : M.nerode s₁ s₂ ↔
    ((M : DFA α σ).accepts).leftQuotient (M.stateToWord s₁) =
    ((M : DFA α σ).accepts).leftQuotient (M.stateToWord s₂) := by
  simp [nerode, Indist]



/- TODO: Prove that -/


/- TODO:  We prove that the transition functin of the nerodeAutomaton is defined by
a function on the left quotients.-/

lemma nerodeAutomaton_lt (M : AccessibleFinDFA α σ) :
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

/-- `M.nerodeAutomaton` accepts the same language as `M` -/
theorem nerodeAutomaton_pres_lang (M : AccessibleFinDFA α σ) :
    (M.nerodeAutomaton : DFA α (Quotient (M.nerode))).accepts = (M : DFA α σ).accepts := by
  suffices h : M.nerodeAutomaton ≤ M by
    obtain ⟨h⟩ := h
    symm
    apply DFA.hom_pres_lang
    exact h.1
  exact nerodeAutomaton_lt M

/-- The nerode automaton is less than all automata that accept the same language.
(more accurately, it is less than all automata for which )-/
theorem nerodeAutomaton_isMinimal (M : AccessibleFinDFA α σ) :
    (M.nerodeAutomaton).IsMinimal := by
  intro σ₂ _ _ N hle
  simp [le] at hle
  rcases hle with ⟨h⟩
  apply Nonempty.intro
  let M' := M.nerodeAutomaton

  have hbij : h.toFun.Bijective := by
    refine (Fintype.bijective_iff_surjective_and_card h.toFun).mpr ?_
    constructor
    · apply h.surjective
    · have hle : Fintype.card σ₂ ≤ Fintype.card (Quotient (M.nerode)) := by
        apply Fintype.card_le_of_surjective h.toFun h.surjective
      refine Nat.le_antisymm ?_ hle
      by_contra hlt

      simp_all

      sorry

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


def IsMinimalAlt (M : AccessibleFinDFA α σ) : Prop :=
  ∀ {σ₂ : Type*} [Fintype σ₂] [DecidableEq σ₂] (N : AccessibleFinDFA α σ₂),
  (N : DFA α σ₂).accepts = (M : DFA α σ).accepts → M.nerodeAutomaton ≤ N


end AccessibleFinDFA

-/

example : 1 + 1 = 2 := by rfl
