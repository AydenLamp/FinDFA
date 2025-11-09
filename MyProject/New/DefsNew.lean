import Mathlib

/-!
# FinDFA: Computable DFAs

This file defines structures `FinDFA` and `AccessibleFinDFA`, and a function
`FinDFA.toAccessible` that converts a `FinDFA` to an `AccessibleFinDFA`. This function is
proven to preserve the language accepted by `FinDFA.toAccessible_pres_lang`.

## Main definitions

* `FinDFA α σ` - A DFA with alphabet `α` and state space `σ`. This is like `DFA α σ`, but with
  the accepting states given as a `Finset σ` rather than a `Set σ`.

* `FinDFA.getWordsLeqLength (n : ℕ)` - Returns a `Finset` of all words of length less than or
  equal to `n` over the alphabet of the `FinDFA`.

* `FinDFA.IsAccessibleState` - A predicate on states, true if the state is reachable from the
  start state by some word.

* `FinDFA.isAccessibleStateDecidable` - A decidability instance for `FinDFA.IsAccessibleState`.

* `AccessibleFinDFA` - A structure extending `FinDFA` with a proof that every state is
  accessible.

* `FinDFA.toAccessible` - A function that converts a `FinDFA` to an `AccessibleFinDFA`.

## Main theorems

* `FinDFA.getWordsLeqLength_correct` - `w ∈ M.getWordsLeqLength n ↔ w.length ≤ n`.

* `FinDFA.exists_short_access_word` - In order to construct `AccessibleFinDFA`s from `FinDFA`s,
  we need to define a decidability instance on `FinDFA.isAccessibleState`. As written, this
  involves searching the infinite space of all words. However, we prove in
  `FinDFA.exists_short_access_word` that, if a state is accessible by any word, then it is
  accessible by some word of length at most the number of states in the `FinDFA`. This allows
  us to search through a finite space of words using our `FinDFA.getWordsLeqLength` function.

* `FinDFA.toAccessible_pres_lang` - The language of a `FinDFA` is the same as the language of
  the `AccessibleFinDFA` obtained by applying `FinDFA.toAccessible`.

## Implementation notes

We provide coercions from `FinDFA` and `AccessibleFinDFA` to `DFA`. This means that when you have
`M : FinDFA α σ` or `M : AccessibleFinDFA α σ`, you can use functions defined on `DFA α σ` such as
`eval`, `evalFrom`, and `accepts` by writing `(M : DFA α σ).eval` or `M.toDFA.eval`.

Note that, just like `DFA`, the definitions of `FinDFA` and `AccessibleFinDFA` do not require the
state space or alphabet to be finite or to have decidable equality.

## Blueprint

* One DEF entry for Mathlib's `DFA`
Label : dfa
Lean definitions to tag : None
Content : Explain that this is Mathlib's DFA defintitoin.
Explain that `DFA α σ` has fields `step`, `start`, `accept`,
and methods `eval`, `evalFrom`, `accepts`. Explain
the types of these.
Explain that this definition does not require the state space or alphabet to be finite or
decidable.
(explain what decidable equality is)
Dependencies : None

* One DEF entry for `FinDFA`
Label : fin-dfa
lean defs :
  - `FinDFA`
Content : Explain the definition of the `FinDFA` structure, and how it differes from `DFA`
by requiring `Fintype` and `DecidableEq` instances on the alphabet and state
space (explain what those classes are)
and by requiring the accepting states to be a `Finset` rather than a `Set` (explain the
differnece)
Explain how this allows a decidable procedure (what is that?)
for determining if a state is accepting. Explain how this can be converted to a `DFA` in
lean and how we use the `DFA` definitions for .evalFrom, .accepts, etc.
Dependencies : None

* One DEF entry for Accessible State and DFA definition
label : accessable-fin-dfa
lean defs :
  - `FinDFA.IsAccessibleState`
  - `AccessibleFinDFA`
Content : Explain the definition of accessible states and the `AccessibleFinDFA` structure.
Dependencies : fin-dfa

* One lemma entry for `FinDFA.exists_short_access_word`
Label : exists-short-access-word
Lean lemmas to tag :
  - `FinDFA.exists_short_access_word`
  - `FinDFA.isAccessibleStateDecidable`
  - `FinDFA.toAccessible`
  - `FinDFA.toAccessible_pres_lang`
Content : Prove it and explain why this means that every word that is
accessible is accessible by a short word.
Explain how this is used to create a DECIDABLE procedure for determining
if a state is accessible. Explain how
that allows for a language-preserving conversion from `FinDFA` to
`AccessibleFinDFA` by restricting the state space.
Dependencies : accessible-fin-dfa
-/

namespace List

variable {α : Type*} [Fintype α] (w : List α)

/-- Given a word, the injection sending each letter to its prepending to that word. -/
abbrev prependInjection : α ↪ List α where
  toFun (a : α) := a :: w
  inj' := by simp_all [Function.Injective]

/-- Given a word, the finset of all one-letter (preprended) extensions. -/
abbrev getNextWords : Finset (List α) :=
  Finset.map w.prependInjection (Finset.univ : Finset α)

variable [DecidableEq α]

/-- Return all words of length at most `n`. -/
@[simp] def getWordsLeqLength (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => {[]}
  | n + 1 =>
    let shorterWords := getWordsLeqLength n
    shorterWords ∪ (shorterWords.biUnion getNextWords)

theorem getWordsLeqLength_correct (n : ℕ) (w : List α) :
    w ∈ getWordsLeqLength n ↔ w.length ≤ n := by
  constructor
  · intro hin
    induction n generalizing w with
    | zero => simp_all [getWordsLeqLength]
    | succ m ih =>
      simp_all [getWordsLeqLength]
      rcases hin with (hin | hin)
      · specialize ih w hin
        omega
      · obtain ⟨v, ⟨hv, ⟨a, ha⟩⟩⟩ := hin
        subst w
        simp
        apply ih
        exact hv
  · intro hlen
    induction n generalizing w with
    | zero => simp_all [getWordsLeqLength]
    | succ n ih =>
      simp_all [getWordsLeqLength]
      have hn : w.length = n + 1 ∨ w.length ≤ n := by
        exact Nat.le_succ_iff_eq_or_le.mp hlen
      rcases hn with (hn | hn)
      · right
        have hw : w ≠ [] := by
          aesop
        have hw' := w.cons_head_tail hw
        use w.tail
        simp_all
        have hw' := w.cons_head_tail hw
        use w.head hw
      · left
        apply ih
        exact hn

end List

namespace DFA

universe u v

variable {α : Type u} {σ : Type v} (M : DFA α σ)

def IsAccessibleState (s : σ) : Prop :=
  ∃ x : List α, M.eval x = s

class Accessible where
  allAccessible (s : σ) : M.IsAccessibleState s

def allAccessible [Accessible M] (s : σ) : M.IsAccessibleState s :=
  Accessible.allAccessible s

def toAccessible : DFA α {s // M.IsAccessibleState s} where
  step s a := ⟨M.step s.val a, by
    obtain ⟨x, hx⟩ := s.prop
    use x ++ [a]
    simp [hx]⟩
  start := ⟨M.start, by use []; simp⟩
  accept := {s | s.val ∈ M.accept}

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

@[simp] lemma toAccessible_accepts_def :
    M.toAccessible.accepts = M.accepts := by simp [accepts, acceptsFrom]

instance toAccessible.Accessible : Accessible (M.toAccessible) where
  allAccessible s := by
    obtain ⟨w, hw⟩ := s.prop
    use w
    simp_all

section AccessibleInduction

variable {M : DFA α σ} [Accessible M]

/-- Induction principle for accessible DFAs: to prove a property P holds for all states,
    it suffices to prove P(M.eval w) for all words w. -/
lemma accessible_induction {P : σ → Prop}
  (h : ∀ w : List α, P (M.eval w)) : ∀ s : σ, P s := by
  intro s
  obtain ⟨w, hw⟩ := M.allAccessible s
  rw [← hw]
  exact h w

lemma accessible_split (s : σ) : s = M.start ∨ ∃ w ≠ [], M.eval w = s := by
  obtain ⟨w, hw⟩ := M.allAccessible s
  by_cases hnil : w = []
  · left
    rw [hnil] at hw
    simp_all
  · right
    use w, hnil, hw

end AccessibleInduction

section Fin

class Fin where
  finAccept : Finset σ
  map_accept : M.accept = ↑finAccept

variable [hFin : Fin M]

@[simp] lemma Fin_mem_accept (s : σ) :
    s ∈ M.accept ↔ s ∈ hFin.finAccept := by simp [hFin.map_accept]

@[simp] lemma Fin_coe_finAccept :
    (hFin.finAccept : Set σ) = M.accept := by simp [hFin.map_accept]

@[simp] lemma Fin_acceptsFrom_def :
    M.acceptsFrom = fun s ↦ {w | M.evalFrom s w ∈ hFin.finAccept} := by
  ext s w
  rw [Set.mem_setOf]
  simp [mem_acceptsFrom]

@[simp] lemma Fin_accepts_def :
    M.accepts = {w | M.eval w ∈ hFin.finAccept} := by
  ext w
  rw [Set.mem_setOf]
  simp [mem_accepts]

end Fin

/-!
### Decidability of IsAccessibleState in FinDFAs

In order to prove that `M.toAccessible` preserves Finiteness (that is, if we can return
the set of accepting states of `M.toAccessible` as a Finset, and we can infer a DecidableEq
and Fintype instance on {s // M.IsAccessibleState s}), we need to show that `M.IsAccessibleState`
is a decidable predicate when `M` has a `Fin` instance and `σ` and `α` have Fintype and DecidableEq
instances.

To to this, we prove that a state is accessible iff it is accessible by some word of length at most
`|σ|`. This allows us to check accessibility by checking a finite number of words.
-/

variable [Fintype σ]

/-- Every accessible state is reachable by a word of length at most the number of states. -/
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

instance IsAccessibleState_decidable : DecidablePred M.IsAccessibleState := by
  intro s
  exact decidable_of_decidable_of_iff (M.IsAccessibleState_iff_in_wordsLeqCard s)

instance toAccessible.Fin [hFin : Fin M] : Fin (M.toAccessible) where
  finAccept := Finset.subtype M.IsAccessibleState hFin.finAccept
  map_accept := by
    ext s
    simp

end DFA
