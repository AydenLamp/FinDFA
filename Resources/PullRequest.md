# Mathlib Contributions

## TODO
- Find references for 
  - definitions of DFA accessibility
  - DFA morphisms

## FinDFA project
- Morphisms of DFAs
  - Minimality Definition
  - Proof `Language.toDFA` is minimal
  - Computable minimization `DFA.minimize`
  - Finpartition refinement lemma?
- Computable DFA typeclass `Fin`
- Accessible DFA typeclass `Accessible`
  - DFA.toAccessible (and computable instances)

## Semigroup Project
- Substructures (how should subsemigroup be named?)
- Ideals
- Greens Relations
- Finite semigroup theorems
- Powers in semigroups!
- Rees Matrix (eventually)

# Notes

Lead with adding the minimization to mathlib rather than the lack of computability 

Mention that this is a stepping stone to the algebraic stuff (transition monoid, synctactic monoid, semigroup theory, aperiodic transition monoid iff star free)

Say minimal atuomaton is an important stepping stone for later results

Take a look at "handbook of automata theory"

# FinDFA project "New Members" post

## Introduction

Hello! I'm Ayden Lamparski, an undergraduate at Boston College working on my thesis under Professor Howard Straubing. I've been developing a formalization of DFA minimization, and I would like to create a Pull Request. However, I am unsure exactly what parts of this project would be suitable for Mathlib.

**Repository**: [GitHub link here]

Mathlib's current DFA implementation in `Mathlib.Computability.DFA` has significant computability limitations. The `DFA` structure defines accepting states as `accept : Set σ`, which is inherently non-computable (there's no algorithmic way to test if a given state is accepting, and thus no way to test if a specific DFA accepts a particular word). Additionally, these DFAs aren't required to be finite: without explicit `Fintype` instances, a "DFA" could theoretically have infinitely many states, and could theoretically recognize non-regular languages. This extends to `Language.toDFA` in `Mathlib.Computability.MyhillNerode`, which constructs a DFA that accepts an arbirtary language. However, the DFA it returns lacks a `Fintype` instance on the type of states, making it algorithmically unusable despite being propositionally correct.

This project provides a typeclass on DFAs `Fin` for making DFA more computable (when combined with `Fintype` and `DecidableEq` instances). We also define operations of DFAs, like `DFA.minimize` that are proven to preserve these instances.

## Content for Potential PR

### `Fin` typeclass on DFAs
For any `M : DFA α σ`, an instance `Fin M` provides:
- `acceptFin : Finset σ` alongside the existing `accept : Set σ`
- Proof that `↑acceptFin = accept` (mathematical equivalence)

When combined with `Fintype`/`DecidableEq` instances, this solves the core computability problem with DFAs (we can now decidably test if a given DFA accepts a given word). 

### 2. `Accessible` typeclass and `DFA.toAccessible`
The `Accessible` typeclass asserts that every state of a DFA is be reachable from the start state by some word. `DFA.toAccessible` restricts a given DFA to its accessible states, and is proven to output a DFA that accepts the same language. We also prove that `toAccessible` preserves computational instances (`Fin`, `Fintype`, `DecidableEq`). In fact, much of the mathmatical content of this section is in the decidability instances, where we must prove that we only have to test a finite amount of words in order to decide if a state is accessible by any word.

### 3. DFA Morphisms and Structural Minimality
I formalize DFA morphisms as structure-preserving bundled functions on their state-types.
We define a partial order on accessible DFAs: `M ≤ N` iff ∃ surjective morphism `N ↠ M`,
We define minimality by minimality in this partial order, rather than the less strict definitoin of simply having the least amount of states of any DFA accepting the same language. 

### 4. Constructive Minimization Algorithm (`DFA.minimize`)
Constructive minimization that solves `Language.toDFA`'s computability issues:
- Produces DFAs equivalent to `M.accepts.toDFA` (equivalent in the sence that we construct a bijective morphism)
- **Unlike `Language.toDFA`**: preserves `Fin`, `Fintype`, and `DecidableEq` instances
- Proves minimality in both structural (morphism) and cardinality senses

## Questions

1. **PR Structure**: Should I submit multiple small PRs (one for DFA morphisms, one for typeclasses, one for minimization) or one larger and more comprehensive PR?

2. **File Organization**: 
Should I extend the existing `Mathlib.Computability.DFA` file or create a new file for DFA typeclasses? Should I creat a new file for DFA minimization or extend `Mathlib.Computability.MyhillNerode`?

3.  Does the constructive nature and computability focus fit into Mathlib? Should I focus more on the definition of Morphisms / the Accessible typeclass more than the minimization algorithm?

Thanks for any advice!
