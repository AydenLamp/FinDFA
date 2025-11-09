import MyProject.New.List
import MyProject.New.Fin

/-!
# Accessible DFAs

Given an `M : DFA α σ`, a state `s : σ` is accessible iff there exists some word
`w : List α` such that `M.eval w = s`. If every state of `M` is accessible, then
`M` is an Accessible DFA.

This file defines a typeclass `Accessible` for Accessible DFAs, and we provide a
function `DFA.toAccessible` for constructing an accessible DFA from any DFA.

## Main Definitions

* `DFA.IsAccessibleState` - A predicate on states, asserting that there exists a word
`w` such that `M.eval w` equals that state.

* `DFA.Accessible` - A typeclass on DFAs asserting that all states are accessible.

* `DFA.toAccessible` - Trim away the non-accessible states of a DFA.

* `DFA.toAccessible_accessible` - An `Accessible` typeclass instance for `M.toAccessible`

* `DFA.toAccessible_decidable` - An instance of `DecidablePred M.isAccessibleState`, given
`Fin M` and `Fintype` and `DecidableEq` instances.

* `DFA.toAccessile_fin` - Given `Fin M` for `M : DFA α σ` and `Fintype` and `DecidableEq` instances
on `α` and `σ`, we obtain the instance `Fin M.toAccessible`.

## Main Theorems

* `DFA.toAccessible_pres_accepts` - The lanuguage of `M` equals the language of `M.toAccessible`

* `DFA.exists_short_access_word` - If a state is accessible, it is accessed by some word of length
less than or equal to the amount of states. This allows us to obtain a decidability instance
for `M.isAccessibleState` by searching over a finite set of words.
-/

namespace DFA

universe u v

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-- A predicate on States of a `DFA` asserting that there exists a word
`w` such that `M.eval w` equals that state -/
def IsAccessibleState (s : σ) : Prop :=
  ∃ w : List α, M.eval w = s

/-- A typeclass on `DFA`s asserting that every state is accessible -/
class Accessible where
  allAccessible (s : σ) : M.IsAccessibleState s

def allAccessible [Accessible M] (s : σ) : M.IsAccessibleState s :=
  Accessible.allAccessible s

/-- Given a `M : DFA α σ`, `M.toAccessible` is `M` but with all
the non-accessible states removed. -/
def toAccessible : DFA α {s // M.IsAccessibleState s} where
  step s a := ⟨M.step s.val a, by
    obtain ⟨x, hx⟩ := s.prop
    use x ++ [a]
    simp [hx]⟩
  start := ⟨M.start, by use []; simp⟩
  accept := {s | s.val ∈ M.accept}

/-- If `s` is accessible, then `M.step s a` is accessible for all `a : α` -/
lemma step_pres_isAccessibleState {s : σ} (hs : M.IsAccessibleState s) (a : α) :
    M.IsAccessibleState (M.step s a) := by
  obtain ⟨x, hx⟩ := hs
  use x ++ [a]
  simp [hx]

@[simp] lemma toAccessible_start_def :
    M.toAccessible.start = ⟨M.start, by use []; simp⟩ := rfl

@[simp] lemma toAccessible_coe_start :
    ↑(M.toAccessible.start) = M.start := rfl

@[simp] lemma toAccessible_step_def :
    M.toAccessible.step = fun s a ↦ ⟨M.step ↑s a, M.step_pres_isAccessibleState s.prop a⟩ := rfl

@[simp] lemma toAccessible_coe_step (s : {s // M.IsAccessibleState s}) (a : α) :
    ↑(M.toAccessible.step s a) = M.step ↑s a := rfl

@[simp] lemma toAccessible_evalFrom_def :
    M.toAccessible.evalFrom = fun s w ↦ ⟨M.evalFrom ↑s w, by
      obtain ⟨w', hw⟩ := s.prop
      use w' ++ w
      simp_all [eval, evalFrom_of_append]⟩ := by
  ext s w
  simp [evalFrom]
  exact Eq.symm (List.foldl_hom Subtype.val fun x ↦ congrFun rfl)

@[simp] lemma toAccessible_coe_evalFrom (s : {s // M.IsAccessibleState s}) (w : List α) :
    ↑(M.toAccessible.evalFrom s w) = M.evalFrom ↑s w := by simp

@[simp] lemma toAccessible_eval_def :
    M.toAccessible.eval = fun w ↦ ⟨M.eval w, by use w⟩ := by simp [eval]

@[simp] lemma toAccessible_coe_eval (w : List α) :
    ↑(M.toAccessible.eval w) = M.eval w := by simp

@[simp] lemma toAccessible_accept_def :
    M.toAccessible.accept = {s | s.val ∈ M.accept} := rfl

@[simp] lemma toAccessible_mem_accept (s : {s // M.IsAccessibleState s}) :
    s ∈ M.toAccessible.accept ↔ ↑s ∈ M.accept := by rfl

@[simp] lemma toAccessible_acceptsFrom_def :
    M.toAccessible.acceptsFrom = fun s ↦ {x | M.evalFrom s.val x ∈ M.accept} := by
  ext s x
  simp [acceptsFrom]

@[simp] lemma toAccessible_pres_accepts :
    M.toAccessible.accepts = M.accepts := by simp [accepts, acceptsFrom]

/-- `M.toAccessible` is an Accessible DFA. -/
instance toAccessible.Accessible : Accessible (M.toAccessible) where
  allAccessible s := by
    obtain ⟨w, hw⟩ := s.prop
    use w
    simp_all

section InductionPrincipals

variable {M : DFA α σ} [Accessible M]

/-- Induction principle for accessible DFAs: to prove a property P holds for all states,
    it suffices to prove P(M.eval w) for all words w. -/
lemma accessible_induction {P : σ → Prop}
  (h : ∀ w : List α, P (M.eval w)) : ∀ s : σ, P s := by
  intro s
  obtain ⟨w, hw⟩ := M.allAccessible s
  rw [← hw]
  exact h w

/-- All states of an `Accessible DFA` are either `M.start` or `M.eval w` for
some `w ≠ []` -/
lemma accessible_split (s : σ) : s = M.start ∨ ∃ w ≠ [], M.eval w = s := by
  obtain ⟨w, hw⟩ := M.allAccessible s
  by_cases hnil : w = []
  · left
    rw [hnil] at hw
    simp_all
  · right
    use w, hnil, hw

end InductionPrincipals

/-!
### Decidability of IsAccessibleState in Finite DFAs

In order to prove that `M.toAccessible` preserves Finiteness (that is, if we can return
the set of accepting states of `M.toAccessible` as a Finset, and we can infer a DecidableEq
and Fintype instance on {s // M.IsAccessibleState s}), we need to show that `M.IsAccessibleState`
is a decidable predicate when `M` has a `Fin` instance and `σ` and `α` have Fintype and DecidableEq
instances.

To to this, we prove that a state is accessible iff it is accessible by some word of length at most
`|σ|`. This allows us to check accessibility by checking a finite number of words.
-/

variable [Fintype σ]

/-- Given that the set of states is finite, every accessible state is reachable by a
word of length at most the number of states. -/
theorem exists_short_access_word (s : σ) {w : List α}
    (hw : M.eval w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ M.eval v = s := by
  -- Strong recursion on the length of `w`
  refine (Nat.strongRecOn
    (motive := fun n => ∀ w : List α, w.length = n → M.eval w = s →
      ∃ v : List α, v.length ≤ Fintype.card σ ∧ M.eval v = s)
    w.length ?_ w rfl hw)
  simp_all
  intro n ih u hlen hu
  by_cases hshort : n ≤ Fintype.card σ
  · subst hlen
    use u
  · have hle : Fintype.card σ ≤ n := by exact Nat.le_of_not_ge hshort
    -- Use Mathlib's `DFA.evalFrom_split` lemma to split `w` into `a ++ b ++ c` with a loop on `b`.
    subst hlen
    have h := (M.evalFrom_split hle hu)
    rcases h with ⟨q, a, b, c, hsplit, hlen, hbne, hqa, hqb, hqc⟩
    simp_all
    have hlen₂ : (a ++ c).length < a.length + (b.length + c.length) := by
      simp_all
      exact List.length_pos_iff.mpr hbne
    specialize ih (a ++ c).length hlen₂ (a ++ c) rfl
    apply ih
    simp [eval, evalFrom_of_append, hqa, hqc]

variable [Fintype α] [DecidableEq α]

/-- A state is accessible iff there exists a word accessing it in the Finset
of all words of length less than or equal to the cardinality of the state-space. -/
lemma IsAccessibleState_iff_in_wordsLeqCard (s : σ) :
    (∃ w ∈ List.getWordsLeqLength (Fintype.card σ), M.eval w = s) ↔ M.IsAccessibleState s := by
  simp [IsAccessibleState]
  constructor
  · rintro ⟨w, _, hw⟩
    use w
  · rintro ⟨w, hw⟩
    obtain ⟨v, hvlen, hv⟩ := M.exists_short_access_word s hw
    use v
    rw [List.getWordsLeqLength_correct (Fintype.card σ) v]
    simp_all

variable [DecidableEq σ]

/-- Given that `M` is finite, `M.IsAccessibleState` is a Decidable Predicate. -/
instance IsAccessibleState_decidable : DecidablePred M.IsAccessibleState := by
  intro s
  exact decidable_of_decidable_of_iff (M.IsAccessibleState_iff_in_wordsLeqCard s)

/-- Given `M` is Finite, `M.toAccessible` has a `Fin` instance. -/
instance toAccessible.Fin [hFin : Fin M] : Fin (M.toAccessible) where
  finAccept := Finset.subtype M.IsAccessibleState hFin.finAccept
  accept_eq := by
    ext s
    simp

end DFA

#min_imports
