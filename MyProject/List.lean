import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.SuccPred

/-!
# Operations on words over finite alphabets (List.lean)

This file defines functions on finsets of words over finite alphabets.

## Main Definitions

* `List.getWordsLeqLength` - Given a finite alphabet and an `n : ℕ`,
returns the `Finset` of all words with length less than or equal to `n`

## Main Theorems

* `List.getWordsLeqLength_correct` - Proves that the words in `List.getWordsLeqLength n`
are prececly the words of length `≤ n`
-/

namespace List

variable {α : Type*} [Fintype α]

/-- Given a word, the injection sending each letter to its prepending to that word. -/
abbrev prependInjection (w : List α) : α ↪ List α where
  toFun (a : α) := a :: w
  inj' := by simp_all [Function.Injective]

/-- Given a word, the finset of all one-letter (preprended) extensions. -/
abbrev getNextWords (w : List α) : Finset (List α) :=
  Finset.map w.prependInjection (Finset.univ : Finset α)

variable [DecidableEq α]

/-- Return all words of length at most `n`. -/
@[simp] def getWordsLeqLength (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => {[]}
  | n + 1 =>
    let shorterWords := getWordsLeqLength n
    shorterWords ∪ (shorterWords.biUnion getNextWords)

/-- `getWordsLeqLength n` contains exactly the words of length `≤ n`. -/
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
