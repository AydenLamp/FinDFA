import Mathlib.Computability.DFA
import Mathlib.Data.Nat.SuccPred

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

end List

universe u v

/-- A computable DFA. Just like `DFA` but `accept` is a `Finset` -/
structure FinDFA (α : Type u) (σ : Type v) where
  /-- Transition function. -/
  step : σ → α → σ
  /-- Start state. -/
  start : σ
  /-- Accepting states as a `Finset`. -/
  accept : Finset σ

namespace FinDFA

variable {α : Type u} {σ : Type v}

/-- Convert a `FinDFA` to a `DFA`. -/
def toDFA (M : FinDFA α σ) : DFA α σ where
  step   := M.step
  start  := M.start
  accept := (M.accept : Set σ)

/-- Coercion from `FinDFA` to `DFA`. -/
instance : Coe (FinDFA α σ) (DFA α σ) := ⟨toDFA⟩

@[simp] lemma coe_start (M : FinDFA α σ) : M.toDFA.start = M.start := rfl

@[simp] lemma coe_step (M : FinDFA α σ) : M.toDFA.step = M.step := rfl

@[simp] lemma coe_accept (M : FinDFA α σ) : M.toDFA.accept = ↑M.accept := by rfl

section GetWordsLeqLength

variable [Fintype α] [DecidableEq α]

/-- Return all words of length `n` in the alphabet. -/
@[simp] def getWordsOfLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => {[]}
  | n + 1 => Finset.biUnion (M.getWordsOfLength n) List.getNextWords

@[simp] lemma getWordsOfLength_correct (M : FinDFA α σ) (n : ℕ) (w : List α) :
    w ∈ M.getWordsOfLength n ↔ w.length = n := by
  constructor
  · intros h
    induction n generalizing w with
    | zero => simp_all
    | succ n ih =>
      simp_all
      obtain ⟨v, ⟨hv₁, hv₂⟩⟩ := h
      have hvlen := ih v hv₁
      obtain ⟨v, hv⟩ := hv₂
      subst w
      subst n
      simp
  · intros h
    induction w generalizing n with
    | nil =>
      subst n
      simp
    | cons w ws ih =>
      subst n
      simp_all

/-- Return all words of length at most `n`. -/
def getWordsLeqLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => M.getWordsOfLength 0
  | n + 1 => (M.getWordsOfLength (n+1)) ∪ M.getWordsLeqLength n

@[simp] theorem getWordsLeqLength_correct (M : FinDFA α σ) {n : ℕ} {w : List α} :
    w ∈ M.getWordsLeqLength n ↔ w.length ≤ n := by
  constructor
  · intro hin
    induction n generalizing w with
    | zero => simp_all [getWordsLeqLength]
    | succ m ih =>
      simp_all [getWordsLeqLength]
      rcases hin with (hin | hin)
      · aesop
      · apply ih at hin
        exact Nat.le_add_right_of_le hin
  · intro hlen
    induction n generalizing w with
    | zero => simp_all [getWordsLeqLength]
    | succ n ih =>
      simp_all [getWordsLeqLength]
      have hn : w.length = n + 1 ∨ w.length ≤ n := by
        exact Nat.le_succ_iff_eq_or_le.mp hlen
      rcases hn with (hn | hn)
      · left
        have hw : w ≠ [] := by
          aesop
        have hw' := w.cons_head_tail hw
        use w.tail
        simp_all
        have hw' := w.cons_head_tail hw
        use w.head hw
      · right
        apply ih
        exact hn

end GetWordsLeqLength

/-! ### Accessible States -/

section AccessibleStates

/-- A state is accessible if there exists some word that reaches it from the start state. -/
abbrev IsAccessibleState (M : FinDFA α σ) (s : σ) : Prop :=
  ∃ w, (M : DFA α σ).evalFrom M.start w = s

/-- Every accessible state is reachable by a word of length at most the number of states. -/
theorem exists_short_access_word [Fintype σ] (M : FinDFA α σ) (s : σ) {w : List α}
    (hw : (M : DFA α σ).evalFrom M.start w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ s = (M : DFA α σ).evalFrom M.start v := by
  -- Strong recursion on the length of `w`
  refine (Nat.strongRecOn
    (motive := fun n => ∀ w : List α, w.length = n →
      (M : DFA α σ).evalFrom M.start w = s →
        ∃ v : List α, v.length ≤ Fintype.card σ ∧
        s = (M : DFA α σ).evalFrom M.start v)
    w.length ?_ w rfl hw)
  simp_all
  intro n ih w hlen hw'
  by_cases hshort : n ≤ Fintype.card σ
  · subst hlen
    use w
    simp [hw', hshort]
  · have hle : Fintype.card σ ≤ n := by exact Nat.le_of_not_ge hshort
    -- Use Mathlib's `DFA.evalFrom_split` lemma to split `w` into `a ++ b ++ c` with a loop on `b`.
    subst hlen
    have h := ((M : DFA α σ).evalFrom_split hle hw')
    rcases h with ⟨q, a, b, c, hsplit, hlen, hbne, hqa, hqb, hqc⟩
    simp_all
    have hlen₂ : (a ++ c).length < a.length + (b.length + c.length) := by
      simp_all
      exact List.length_pos_iff.mpr hbne
    have h := ih (a ++ c).length hlen₂ (a ++ c) rfl
    have h' : M.toDFA.evalFrom M.start (a ++ c) = s := by
      simp_all [DFA.evalFrom_of_append]
    obtain ⟨v, hv⟩ := h h'
    use v

variable [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]

/-- The finset of all accessible states. -/
def getAccessibleStates (M : FinDFA α σ) : Finset σ :=
  Finset.biUnion
    (M.getWordsLeqLength (Fintype.card σ))
    (fun s ↦ {(M : DFA α σ).evalFrom M.start s})

/-- Characterization of accessible states. -/
@[simp] lemma getAccessibleStates_correct (M : FinDFA α σ) (s : σ) :
   (s ∈ M.getAccessibleStates) ↔ M.IsAccessibleState s := by
  simp [IsAccessibleState, getAccessibleStates]
  constructor
  · rintro ⟨w, hw₁, hw₂⟩
    use w
    exact hw₂.symm
  · rintro ⟨w, hw⟩
    apply M.exists_short_access_word s hw

/-- Decidability of state accessibility. -/
instance isAccessibleStateDecidable (M : FinDFA α σ) :
    DecidablePred (M.IsAccessibleState) := by
  intros s
  apply decidable_of_decidable_of_iff (M.getAccessibleStates_correct s)

end AccessibleStates

end FinDFA

/-! ### Accessible DFAs -/

/-- A DFA where every state is accessible from the start state. -/
structure AccessibleFinDFA (α : Type u) (σ : Type v) extends M : FinDFA α σ where
  is_accessible (s : σ) : M.IsAccessibleState s

namespace AccessibleFinDFA

variable {α : Type u} {σ : Type v}

/-- Convert an `AccessibleFinDFA` to a `FinDFA`. -/
@[simp] def toFinDFA (M : AccessibleFinDFA α σ) : FinDFA α σ where
  step   := M.step
  start  := M.start
  accept := M.accept

/-- Convert an `AccessibleFinDFA` to a `DFA`. -/
@[simp] def toDFA (M : AccessibleFinDFA α σ) : DFA α σ := M.toFinDFA.toDFA

/-- Coercion from `AccessibleFinDFA` to `FinDFA`. -/
instance : Coe (AccessibleFinDFA α σ) (FinDFA α σ) := ⟨toFinDFA⟩

@[simp] lemma coe_start' (M : AccessibleFinDFA α σ) : M.toFinDFA.start = M.start := by rfl

@[simp] lemma coe_step' (M : AccessibleFinDFA α σ) : M.toFinDFA.step = M.step := by rfl

@[simp] lemma coe_accept' (M : AccessibleFinDFA α σ) : M.toFinDFA.accept = M.accept := by rfl

/-- Coercion from `AccessibleFinDFA` to `DFA`. -/
instance : Coe (AccessibleFinDFA α σ) (DFA α σ) := ⟨toDFA⟩

@[simp] lemma coe_start (M : AccessibleFinDFA α σ) : M.toDFA.start = M.start := by rfl

@[simp] lemma coe_step (M : AccessibleFinDFA α σ) : M.toDFA.step = M.step := by rfl

@[simp] lemma coe_accept (M : AccessibleFinDFA α σ) : M.toDFA.accept = ↑M.accept := by rfl

end AccessibleFinDFA

/-!
### FinDFA → AccessibleFinDFA

By restricting the state space to only the accessible states, we can convert any `FinDFA` to an
`AccessibleFinDFA`. We prove that this conversion preserves the language accepted by the DFA.
-/

namespace FinDFA

variable {α : Type u} {σ : Type v}

variable [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]

/-- Convert a `FinDFA` to an `AccessibleFinDFA` by restricting to accessible states. -/
def toAccessible (M : FinDFA α σ) :
    AccessibleFinDFA α {s : σ // M.IsAccessibleState s} where
  step := fun s a => ⟨M.step s.val a, by
      simp_all [IsAccessibleState]
      obtain ⟨s, ⟨w, hs⟩⟩ := s
      use w ++ [a]
      simp_all⟩
  start := ⟨M.start, by simp_all only [IsAccessibleState]; use []; simp⟩
  accept := {s | s.val ∈ M.accept}
  is_accessible := by
    rintro ⟨s, ⟨w, hs⟩⟩
    simp_all [IsAccessibleState]
    use w
    apply Subtype.eq
    simp_all [toDFA]
    induction w using List.reverseRecOn generalizing s with
    | nil => simp_all
    | append_singleton w a ih => simp_all [toDFA]

variable (M : FinDFA α σ)

@[simp] lemma toAccessible_step_val (s : {s : σ // M.IsAccessibleState s}) (a : α) :
    ((M.toAccessible).step s a).val = M.step s.val a := rfl

/-- Evaluating `toAccessible` from an accessible state matches the original evaluation. -/
lemma toAccessible_evalFrom_val (s : {s : σ // M.IsAccessibleState s}) (w : List α) :
    ((M.toAccessible : DFA α {s : σ // M.IsAccessibleState s}).evalFrom s w).val
      = ((M : DFA α σ).evalFrom s.val w) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [DFA.evalFrom]
  | append_singleton w a ih =>
    simp_all [DFA.evalFrom_append_singleton]

/-- Evaluating `toAccessible` from the start matches the original evaluation. -/
lemma toAccessible_eval_val (w : List α) :
    ((M.toAccessible : DFA α {s : σ // M.IsAccessibleState s}).eval w).val
      = ((M : DFA α σ).eval w) := by
  have h := M.toAccessible_evalFrom_val ((M.toAccessible : AccessibleFinDFA α _).start) w
  simp_all [DFA.eval, toAccessible]

/-- The language accepted by `toAccessible` equals the language accepted by the original DFA. -/
theorem toAccessible_pres_lang :
    ((M.toAccessible) : DFA α {s : σ // M.IsAccessibleState s}).accepts =
      (M : DFA α σ).accepts := by
  ext w
  have h := M.toAccessible_eval_val w
  simp_all [DFA.mem_accepts]
  rw [← h]; clear h
  simp_all [toAccessible]

end FinDFA
