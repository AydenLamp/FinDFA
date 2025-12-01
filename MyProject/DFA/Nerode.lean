import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import MyProject.DFA.Fin
import MyProject.List

/-!
# Nerode Equivalence on AccessibleFinDFAs

This file defines the Nerode equivalence relation on the states of a DFA.
Two states `s₁, s₂` are Nerode equivalent if the set of words `w` such that `M.evalFrom s₁ w`
is an accepting state is equal to the set words such that `M.evalFrom s₂ w` is accepting.

We also establish the decidability of the nerode equivalence, given an instance `Fin M` and
Fintype and DecidableEq instances on the state-space and alphabet. A priori, this would
require checking infinitely many words. However, we define a computable version `DFA.BoundedNeroe n`
which only checks that `M.evalFrom s₁ w ∈ M.acceptFin ↔ M.evalFrom s₁ w ∈ M.acceptFin` for words
`w` such that `w.length ≤ n`. We then prove that `DFA.BoundedNerode |σ| = DFA.Nerode` and
transfer the decidability instance.

In order to prove the equivalence `DFA.boundedNerode |σ| = DFA.nerodeEquiv`, we establish that
`DFA.boundedNerode` is monotone decreasing in `n`, and that it eventually stabilizes at some `n`
(that is, there is some `n` such that, for all `m ≥ n`, `boundedNerode n = boundedNerode m`).
We prove that the stabilized bounded nerode equivalence is equal to the nerode equivalence, and
we use an argument on the finpartitions of the state space induced by boundedNerode to establish
that it must stabilize at or before `n = |σ|`.

## Main Definitions

* `DFA.nerodeEquiv` - The equivalence relation (as a `Setoid`) on states of a `DFA` asserting
that `M.acceptsFrom s₁ = M.acceptsFrom s₂`

* `DFA.nerodeEquiv_decidable` - Decidability instance for `M.nerodeEquiv`, given `Fin M` and
Fintype and DecidableEq instances on the state-space and alphabet of `M`.

## Implementation Notes

We make all definitions and lemmas related to `DFA.boundedNerode` private, becuase they only
serve to obtain the decidability instance on `DFA.nerodeEquiv`, and should not need to be
accessed by other files.

## Refrences

TODO
-/

namespace DFA

universe u v

variable {α : Type u} {σ : Type v} (M : DFA α σ)

def nerodeEquiv : Setoid σ where
  r (s₁ s₂ : σ) : Prop := M.acceptsFrom s₁ = M.acceptsFrom s₂
  iseqv :=  {
    refl (s : σ) := rfl
    symm {s₁ s₂ : σ} hs := hs.symm
    trans {s₁ s₂ s₃ : σ} h₁ h₂ := by rw [h₁, h₂]
  }

/-- A word indistinguishes two states if evaluating from them leads to the same acceptance
outcomes. -/
private def Indist (w : List α) (s₁ s₂ : σ) : Prop :=
  (M.evalFrom s₁ w ∈ M.accept) ↔ (M.evalFrom s₂ w ∈ M.accept)

/-- `a :: w` indistinguishes `s₁` from `s₂` iff `w` indistinguishes
`M.step s₁ a` from `M.step s₂ a`. -/
private lemma indist_cons (w : List α) (a : α) (s₁ s₂ : σ) :
    M.Indist (a :: w) s₁ s₂ ↔ M.Indist w (M.step s₁ a) (M.step s₂ a) := by
  simp_all [Indist, DFA.evalFrom]

/-- The bounded Nerode equivalence at level `n`: two states are equivalent if they are
indistinguishable by words of length ≤ `n`. -/
private def boundedNerode (n : ℕ) : Setoid σ where
  r (s₁ s₂ : σ) : Prop := ∀ w : List α, w.length ≤ n → M.Indist w s₁ s₂
  iseqv := {
    refl := fun s w h => by simp [Indist]
    symm := fun h w hl => by simp [Indist] at *; exact (h w hl).symm
    trans := fun h₁ h₂ w hw => by
      simp [Indist] at *
      rw [h₁ w hw, h₂ w hw] }

/-- Two states are nerode equivalent iff they are
bounded nerode equivalent for all `n` -/
private lemma boundedNerode_forall_eq_nerode (s₁ s₂ : σ) :
    (∀ n, M.boundedNerode n s₁ s₂) ↔ M.nerodeEquiv s₁ s₂ := by
  simp_all [nerodeEquiv, boundedNerode, Indist, acceptsFrom, Language.ext_iff]
  conv => rhs; intro; rw [Set.mem_setOf]; rw [Set.mem_setOf]
  constructor
  · rintro h w
    apply (h w.length)
    simp
  · rintro h n w hw
    apply h

/-!
### Decidability of boundedNerode

We define a computable version of `boundedNerode` that quantifies over our finset
`M.getWordsLeqLength n`. Because this is a finite set, this version is decidable.
We then prove that this computable version is equivalent to the original one, and
thus we can transfer the decidability instance to `boundedNerode`.
-/

section Decidability

variable [Fintype α] [DecidableEq α]

/-- Computable version of bounded Nerode that quantifies over a `Finset` of words. -/
private def BoundedNerodeComputable (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w ∈ List.getWordsLeqLength n, M.Indist w s₁ s₂

/-- The computable version is equivalent to the original bounded Nerode relation. -/
private lemma boundedNerodeComputable_correct (n : ℕ) (s₁ s₂ : σ) :
    M.BoundedNerodeComputable n s₁ s₂ ↔ M.boundedNerode n s₁ s₂ := by
  constructor
  · intro h w hw
    apply h
    rw [List.getWordsLeqLength_correct]
    exact hw
  · intro h w hw
    apply h
    rw [List.getWordsLeqLength_correct] at hw
    exact hw

variable [Fintype σ] [DecidableEq σ] [Fin M]

private instance boundedNerodeComputable_decidable (n : ℕ) :
    DecidableRel (M.BoundedNerodeComputable n) := by
  unfold BoundedNerodeComputable Indist
  simp
  infer_instance

/-- Decidability instance for bounded Nerode. -/
private instance boundedNerode_decidable (n : ℕ) : DecidableRel (M.boundedNerode n) := by
  intros s₁ s₂
  apply decidable_of_iff
    (M.BoundedNerodeComputable n s₁ s₂)
    (M.boundedNerodeComputable_correct n s₁ s₂)

end Decidability

/-!
### BoundedNerode Monotonicity and Stabilization

We say that `boundedNerode` is stable at level `n` if `boundedNerode n = boundedNerode (n + 1)`.
We prove that, if `boundedNerode n` is stable, then `boundedNerode n = boundedNerode m`
for all `m ≥ n` and thus `boundedNerode n = nerodeEquiv`.
-/

/-- Monotonicity of bounded Nerode. -/
private theorem boundedNerode_mono {n m : ℕ} (hle : n ≤ m) :
    M.boundedNerode m ≤ M.boundedNerode n := by
  simp [Setoid.le_def, boundedNerode]
  intros s₁ s₂ h₁ w h₂
  apply h₁
  omega

private theorem boundedNerode_of_ge {n m : ℕ} {s₁ s₂} (h : M.boundedNerode n s₁ s₂) (hle : m ≤ n) :
    M.boundedNerode m s₁ s₂ := by
  have hmono := M.boundedNerode_mono hle
  exact hmono h

/-- If `boundedNerode n` is not equal to `boundedNerode (n+1)`, then there exist states `s₁, s₂`
which are indistinguishable by words of length ≤ `n` but distinguished by some word of
length `n + 1`. -/
private lemma boundedNerode_neq_implies_distinguishes {n : ℕ}
  (hneq : M.boundedNerode n ≠ M.boundedNerode (n + 1)) :
    ∃ (s₁ s₂ : σ), M.boundedNerode n s₁ s₂ ∧
      ∃ (w : List α), (w.length = n + 1) ∧ ¬ (M.Indist w s₁ s₂) := by
  by_contra hexists
  apply hneq
  ext s₁ s₂; constructor
  · intros h
    simp_all
    have h₂ := hexists s₁ s₂ h
    simp_all only [boundedNerode]
    intros w hw
    have hw : w.length = n + 1 ∨ w.length ≤ n := by omega
    rcases hw with (hw | hw)
    · apply h₂; exact hw
    · apply h; exact hw
  · intros h
    apply M.boundedNerode_of_ge h
    simp

/-- If bounded Nerode stabilizes, then so does `boundedNerode (n+1)`. -/
private lemma boundedNerode_stable_succ (n : ℕ)
  (heq : M.boundedNerode n = M.boundedNerode (n + 1)) :
    M.boundedNerode (n + 1) = M.boundedNerode (n + 2) := by
  by_contra hneq
  obtain ⟨s₁, s₂, hind, w, wlen, hdist⟩ := M.boundedNerode_neq_implies_distinguishes hneq
  have hwPos : w ≠ [] := by aesop
  have hw : w = w.head hwPos :: w.tail := by rw [List.cons_head_tail hwPos]
  rw [hw] at hdist
  have hw₁ : w.tail.length = n + 1 := by simp; omega
  rw [indist_cons] at hdist
  have hdist' : ¬ M.boundedNerode (n + 1) (M.step s₁ (w.head hwPos))
      (M.step s₂ (w.head hwPos)) := by
    simp [boundedNerode]
    use w.tail; constructor
    · omega
    · exact hdist
  have hdist'' : ¬ M.boundedNerode n (M.step s₁ (w.head hwPos))
      (M.step s₂ (w.head hwPos)) := by
    rw [heq]; exact hdist'
  simp [boundedNerode] at hdist''
  obtain ⟨t, htlen, htdist⟩ := hdist''
  rw [← indist_cons] at htdist
  have hdist''' : ¬ M.boundedNerode (n + 1) s₁ s₂ := by
    simp [boundedNerode]
    use (w.head hwPos :: t); constructor
    · simp [htlen]
    · exact htdist
  contradiction

/-- If bounded Nerode stabilizes at level `n`, it remains stable for all higher levels. -/
private lemma boundedNerode_stable {n : ℕ} (heq : M.boundedNerode n = M.boundedNerode (n + 1)) :
    ∀ m ≥ n, M.boundedNerode n = M.boundedNerode m := by
  intros m hle
  induction hd : (m - n) generalizing m n heq with
  | zero =>
    have heq : m = n := by grind
    simp_all
  | succ o ih =>
    have heq' := M.boundedNerode_stable_succ n heq
    have hm : m - (n + 1) = o := by omega
    have ih := @ih (n + 1) heq' m (by omega) hm
    rwa [← ih]


/-- If bounded Nerode stabilizes at `n`, then it equals the Nerode equivalence. -/
private lemma boundedNerode_stable_eq_nerode {n : ℕ}
  (heq : M.boundedNerode n = M.boundedNerode (n + 1)) :
    M.boundedNerode n = M.nerodeEquiv := by
  have h := M.boundedNerode_stable heq
  ext s₁ s₂
  rw [← M.boundedNerode_forall_eq_nerode]
  constructor
  · intro h' m
    have h' : m ≥ n ∨ m < n := by omega
    rcases h' with (h'' | h'')
    · have h := h m h''
      rw [← h]; exact h'
    · have hge : m ≤ n := by omega
      apply M.boundedNerode_mono hge
      exact h'
  · intro h; apply h

/-!
### boundedNerode Finpartitions

In this section, we define the `Finpartition` on the state space induced by `boundedNerode n`,
where each part corresponds to an equivalence class of `boundedNerode n`.

We prove that if two bounded Nerode finpartitions have the same cardinality, they have the same
parts and thus induce the same equivalence relation. We then show that the finpartition induced
by `boundedNerode n` has at most `|σ|` parts, and thus the partition must stabilize by level `|σ|`.
-/

section Finpartitions

variable [σFin : Fintype σ] [DecidableEq σ] [Fintype α] [DecidableEq α] [Fin M]

/-- The finpartition of the state space induced by bounded Nerode at level `n`. -/
private def boundedNerodeFinpartition (n : ℕ) : Finpartition (@Finset.univ σ σFin) :=
  Finpartition.ofSetoid (M.boundedNerode n)

/-- Membership in a partition part is equivalent to bounded Nerode equivalence. -/
@[simp] private lemma boundedNerodeFinpartition_mem (n : ℕ) (s₁ s₂ : σ) :
    s₂ ∈ (M.boundedNerodeFinpartition n).part s₁ ↔ M.boundedNerode n s₁ s₂ := by
  simp [boundedNerodeFinpartition, Finpartition.mem_part_ofSetoid_iff_rel]

private lemma boundedNerodeFinpartition_mono {n m : ℕ} (hle : n ≤ m) :
    M.boundedNerodeFinpartition m ≤ M.boundedNerodeFinpartition n := by
  intros t ht
  have hnonempty := Finpartition.nonempty_of_mem_parts (M.boundedNerodeFinpartition m) ht
  rcases hnonempty with ⟨s, hs⟩
  have ht' : (M.boundedNerodeFinpartition m).part s = t := by
    apply Finpartition.part_eq_of_mem
    · exact ht
    · exact hs
  use (M.boundedNerodeFinpartition n).part s
  simp
  intros s₂ hs₂
  rw [boundedNerodeFinpartition_mem]
  have ht' : M.boundedNerode m s s₂ := by
    rwa [← ht', boundedNerodeFinpartition_mem] at hs₂
  have hmono := M.boundedNerode_mono hle
  simp [Setoid.le_def] at hmono
  exact @hmono s s₂ ht'

/-- If two finpartitions have the same cardinality, then they have the same parts. -/
private lemma boundedNerodeFinpartition_parts_eq_of_card_eq {n m : ℕ}
  (hcard : (M.boundedNerodeFinpartition n).parts.card =
    (M.boundedNerodeFinpartition m).parts.card) :
    (M.boundedNerodeFinpartition n).parts = (M.boundedNerodeFinpartition m).parts := by
  wlog hlt : n < m
  · have hlt_or_eq : m < n ∨ n = m := by omega
    rcases hlt_or_eq with (hlt | heq)
    · symm; apply this M hcard.symm hlt
    · rw [heq]
  have hle : n ≤ m := by omega
  let P := M.boundedNerodeFinpartition n
  let Q := M.boundedNerodeFinpartition m
  have hcard : P.parts.card = Q.parts.card := hcard
  have href : Q ≤ P := boundedNerodeFinpartition_mono M hle
  let S := fun (p : Finset σ) ↦ {q ∈ Q.parts | q ⊆ p}
  have union_eq : Q.parts = P.parts.biUnion fun p ↦ S p := by
    unfold S; ext t; constructor
    · intro ht
      refine Finset.mem_biUnion.mpr ?_
      obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := href ht
      use c; simp_all
    · intro ht
      rw [Finset.mem_biUnion] at ht
      obtain ⟨p, hp, ht'⟩ := ht
      simp_all
  have S_eq : ∀ i (hi : i ∈ P.parts), S i = {i} := by
    have hnonempty : ∀ i ∈ P.parts, i.Nonempty := by
      intros i hi
      apply Finpartition.nonempty_of_mem_parts P hi
    have hnonempty' : ∀ i ∈ P.parts, (S i).Nonempty := by
      intros i hi
      obtain ⟨s, hs⟩ := hnonempty i hi
      have hi_eq : P.part s = i := Finpartition.part_eq_of_mem P hi hs
      subst hi_eq
      simp [S]
      use Q.part s; simp
      intros x hx
      rw [boundedNerodeFinpartition_mem] at hx ⊢
      have hle : n ≤ m := by omega
      apply M.boundedNerode_mono hle hx
    have card_one : ∀ p ∈ P.parts, (S p).card = 1 := by
      intros p hp
      have card_pos : ∀ p ∈ P.parts, 1 ≤ (S p).card := by
        intros p hp; simp
        apply hnonempty' p hp
      have card_le : (S p).card ≤ 1 := by
        by_contra hgt
        simp at hgt
        have hcard_eq : (P.parts.biUnion fun p ↦ S p).card = ∑ p ∈ P.parts, (S p).card := by
          refine Finset.card_biUnion ?_
          intros s₁ hs₁ s₂ hs₂ hne p hp₁ hp₂
          simp [S] at hp₁ hp₂
          simp
          refine Finset.eq_empty_of_forall_notMem ?_
          intros x hx
          have hx₁ : x ∈ {q ∈ Q.parts | q ⊆ s₁} := hp₁ hx
          have hx₂ : x ∈ {q ∈ Q.parts | q ⊆ s₂} := hp₂ hx
          simp [Finset.mem_filter] at hx₁ hx₂
          have x_nonempty : x.Nonempty := Finpartition.nonempty_of_mem_parts Q hx₁.1
          obtain ⟨s, hs⟩ := x_nonempty
          have hs₁_mem : s ∈ s₁ := hx₁.2 hs
          have hs₂_mem : s ∈ s₂ := hx₂.2 hs
          apply hne
          exact Finpartition.eq_of_mem_parts P hs₁ hs₂ hs₁_mem hs₂_mem
        have hsum₁ : P.parts.card = ∑ p ∈ P.parts, 1 := by simp
        have hsum₂ : ∑ p ∈ P.parts, 1 < ∑ p ∈ P.parts, (S p).card := by
          apply Finset.sum_lt_sum
          · exact card_pos
          · use p
        rw [← hsum₁, ← hcard_eq, ← union_eq ] at hsum₂
        omega
      specialize card_pos p hp
      omega
    intros i hi
    by_contra hne
    have hexists : ∃ j, S i = {j} := Finset.card_eq_one.mp (card_one i hi)
    obtain ⟨j, hj⟩ := hexists
    have hji : j ⊆ i := by
      simp [S] at hj
      have hj' : j ∈ {q ∈ Q.parts | q ⊆ i} := by rw [hj]; simp
      rw [Finset.mem_filter] at hj'
      exact hj'.2
    have hneq : j ≠ i := by simp_all
    have hexists' : ∃ s ∈ i, s ∉ j := by
      by_contra hne; simp_all
      apply hneq
      exact Finset.Subset.antisymm hji hne
    obtain ⟨s, hsi, hsj⟩ := hexists'
    have hpart : Q.part s ∈ S i := by
      simp [S]
      intros x hx
      rw [boundedNerodeFinpartition_mem] at hx
      have hi_eq : P.part s = i := Finpartition.part_eq_of_mem P hi hsi
      rw [← hi_eq, boundedNerodeFinpartition_mem]
      have hle : n ≤ m := by omega
      apply boundedNerode_mono M hle; exact hx
    have hneq' : Q.part s ≠ j := by
      intro heq
      rw [← heq] at hsj
      have hin : s ∈ Q.part s := by simp
      contradiction
    apply hneq'
    rw [hj] at hpart; simp at hpart; exact hpart
  have parts_subset₁ : Q.parts ⊆ P.parts := by
    intros s hs
    rw [union_eq] at hs; simp_all
    obtain ⟨p, ⟨hp₁, hp₂⟩⟩ := hs
    rw [S_eq] at hp₂
    · have hs : s = p := Finset.eq_of_mem_singleton hp₂
      rw [hs]; exact hp₁
    · exact hp₁
  have parts_subset₂ : P.parts ⊆ Q.parts := by
    intros s hs
    rw [union_eq]
    have hss : S s = {s} := S_eq s hs
    refine Finset.mem_biUnion.mpr ?_
    use s; simp_all
  exact Finset.Subset.antisymm parts_subset₂ parts_subset₁

/-- If two finpartitions have the same cardinality, they induce the same underlying relation. -/
private lemma boundedNerodeFinpartition_eq_of_card_eq {n m : ℕ}
  (hcard : (M.boundedNerodeFinpartition n).parts.card =
           (M.boundedNerodeFinpartition m).parts.card) :
    M.boundedNerode n = M.boundedNerode m := by
  have hparts := boundedNerodeFinpartition_parts_eq_of_card_eq M hcard
  have hpartition : (M.boundedNerodeFinpartition n) = (M.boundedNerodeFinpartition m):= by
    ext s; rw [hparts]
  ext s₁ s₂
  rw [← boundedNerodeFinpartition_mem, ← boundedNerodeFinpartition_mem, hpartition]

/-- Every bounded Nerode finpartition has at least one part. -/
private lemma boundedNerodeFinpartition_card_pos (n : ℕ) :
    1 ≤ (M.boundedNerodeFinpartition n).parts.card := by
  simp
  refine Finset.nonempty_iff_ne_empty.mp ?_
  use M.start; simp

/-- Either `boundedNerodeFinpartition n` has stabilized or it has at least `n + 1` parts. -/
private lemma boundedNerodeFinpartition_stabilized_or_card_ge (n : ℕ) :
    (M.boundedNerodeFinpartition n).parts.card =
      (M.boundedNerodeFinpartition (n + 1)).parts.card ∨
    n < (M.boundedNerodeFinpartition n).parts.card := by
  induction n with
  | zero =>
    right
    have h := boundedNerodeFinpartition_card_pos M 0
    omega
  | succ o ih =>
    rcases ih with (h | h)
    · left
      have heq := boundedNerodeFinpartition_eq_of_card_eq M h
      have heq' : M.boundedNerode (o + 1) = M.boundedNerode (o + 2) := by
        apply boundedNerode_stable_succ M o heq
      simp_all [boundedNerodeFinpartition]
    · have hcard : (M.boundedNerodeFinpartition o).parts.card ≤
          (M.boundedNerodeFinpartition (o + 1)).parts.card := by
        apply Finpartition.card_mono
        apply boundedNerodeFinpartition_mono M; simp
      rw [le_iff_lt_or_eq] at hcard
      rcases hcard with (hlt | heq)
      · right; omega
      · left
        have heq' : M.boundedNerode (o + 1) = M.boundedNerode (o + 2) := by
          refine boundedNerode_stable_succ M o ?_
          apply boundedNerodeFinpartition_eq_of_card_eq M heq
        simp [boundedNerodeFinpartition, heq']

/-- Every bounded Nerode finpartition has at most `|σ|` parts. -/
private lemma boundedNerodeFinpartition_card_le (n : ℕ) :
    (M.boundedNerodeFinpartition n).parts.card ≤ Fintype.card σ := by
  apply Finpartition.card_parts_le_card

/-- The bounded Nerode finpartition stabilizes by level `|σ|`. -/
private lemma boundedNerodeFinpartition_stabilized :
    (M.boundedNerodeFinpartition (Fintype.card σ )).parts.card =
    (M.boundedNerodeFinpartition (Fintype.card σ + 1)).parts.card := by
  have h := boundedNerodeFinpartition_stabilized_or_card_ge M (Fintype.card σ)
  rcases h with (h | h)
  · exact h
  · by_contra
    have hcontra := boundedNerodeFinpartition_card_le M (Fintype.card σ)
    omega

/-- The bounded Nerode relation at level `|σ|` equals the unbounded Nerode relation. -/
private theorem boundedNerode_iff_nerode (s₁ s₂ : σ) :
    M.boundedNerode (Fintype.card σ) s₁ s₂ ↔ M.nerodeEquiv s₁ s₂ := by
  have hstabilized := boundedNerodeFinpartition_stabilized M
  have heq := boundedNerodeFinpartition_eq_of_card_eq M hstabilized
  have heq' := by apply boundedNerode_stable_eq_nerode M heq
  rw [heq']

/-! ### Decidability of Nerode Equivalence -/

/-- Decidability instance for testing if two states of a Fin DFA are
Nerode equivalent. -/
instance nerode_decidable : DecidableRel (M.nerodeEquiv) := by
  intros s₁ s₂
  apply decidable_of_decidable_of_iff (M.boundedNerode_iff_nerode s₁ s₂)

/-- A `Fintype` instance on the quotient of states by Nerode equivalence. -/
instance nerode_quotient_fintype : Fintype (Quotient (M.nerodeEquiv)) := by
  apply @Quotient.fintype σ σFin (M.nerodeEquiv) (nerode_decidable M)

/-- A `DecidableEq` instance on the quotient of states by Nerode equivalence. -/
instance nerode_quotient_decidableEq : DecidableEq (Quotient (M.nerodeEquiv)) := by
  apply @Quotient.decidableEq σ (M.nerodeEquiv) (nerode_decidable M)

end Finpartitions

end DFA
