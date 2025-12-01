import Mathlib.Computability.DFA

/-!
# Finite DFAs

This file defines a typeclass `Fin` on DFAs, which provides a `Finset` for the
accepting states of a DFA, which is typically a `set`. When combined with
`Fintype` and `DecidableEq` instances on the state space and alphabet, this allows for
decidable procedures involving deciding membership in the set of accepting states.

## Main Definitions

`DFA.Fin` - A typeclass on DFAs, which provides the set of accepting states as a `Finset`.

## Implementation Notes

We regester simp lemmas for characterizing `M.accepts` and `M.acceptsFrom` in terms of
our Finset of accepting states `finAccept` from the typeclass `Fin` rather than the DFA's
set of accepting states `M.accept`.

Note that, even with an instance of `Fin M`, `M` may still not be an actually Finite DFA.
In order to have a true DFA, with a finite amount of states and a finite alphabet, one should
provide `Finite` or `Fintype` instances on `σ` and `α`. If you want to be able to define
computable procedures on DFAs, for example to decide whether two states are the same, you
also will need `DecidableEq` instances.
-/

namespace DFA

variable {α : Type*} {σ : Type*} (M : DFA α σ)

/-- A Typeclass on `DFA` providing the set of accepting states as a `Finset`
rather than a `Set` -/
class Fin (M : DFA α σ) where
  /-- The Finset of accepting states -/
  finAccept : Finset σ
  /-- The Finset of accepting states equals the DFA's set of accepting states -/
  accept_eq : M.accept = ↑finAccept

variable [hFin : Fin M]

@[simp] lemma Fin_mem_accept (s : σ) :
    s ∈ M.accept ↔ s ∈ hFin.finAccept := by simp [hFin.accept_eq]

@[simp] lemma Fin_coe_finAccept :
    (hFin.finAccept : Set σ) = M.accept := by simp [hFin.accept_eq]

/-- A characterization of the language of words `w` such that evaluating `w` from
state `s` is accepting in terms of `finAccept` rather than `accept` -/
@[simp] lemma Fin_acceptsFrom_def :
    M.acceptsFrom = fun s ↦ {w | M.evalFrom s w ∈ hFin.finAccept} := by
  ext s w
  rw [Set.mem_setOf]
  simp [mem_acceptsFrom]

/-- A characterization of the language of `M` in terms of `finAccept` rather
than `accept` -/
@[simp] lemma Fin_accepts_def :
    M.accepts = {w | M.eval w ∈ hFin.finAccept} := by
  ext w
  rw [Set.mem_setOf]
  simp [mem_accepts]

end DFA
