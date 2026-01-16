/-!
# Project overview

This repository contains a formalization of the minimization of Deterministic Finite Automata (DFA)
in the Lean 4 theorem prover.

## What is Lean 4?

Lean 4 is an interactive theorem prover (ITP) and programming language.

Unlike traditional programming languages, Lean is based on *dependent type theory*, which allows
types to depend on values. This enables Lean to serve as both a programming language
and a proof assistant: programs can carry proofs of their correctness as part of their types.

Lean uses the *Curry-Howard correspondence*, also called "propositions as types", where
propositions are represented as types and proofs are represented as terms inhabiting those types.
For example, a proof of `A ∧ B` (A and B) is a pair containing a proof of `A` and a proof of `B`.

Lean stands out among ITPs for its focus on formalizing mathmatics and community tooling.

## What is Mathlib?

Mathlib is the mathematical library for Lean, containing over 1.5 million lines of formalized
mathematics. It is the largest unified mathematical library for any theorem prover, covering
algebra, analysis, number theory, and some automata theory.

## Motivation for the project

Mathlib already contains a definition of DFAs (Deterministic Finite Automata) and some basic lemmas
about them (like the pumping lemma), but contains no definitions or theorems about DFA
accessibility, morphisms, or minimization.

This project aims to fill that gap by providing a formalization of these concepts.

## Reading Lean Code

This document contains Lean code snippets. Here is a brief guide to reading them:

- `def` defines a function or value
- `theorem` / `lemma` defines a proof of a proposition
- `by` introduces a tactic proof
- `→` (in type signitures) is the function arrow and also used for implication
- `: Type` and `: Prop` are type annotations
- `[...]` in function signatures are *instance arguments* (typeclasses, explained below)

## What is a DFA?

DFAs are machines that pattern match on strings. Defined on an alphabet (`α`), they either accept
or reject strings of words over that alphabet. In this way, they define a language, which is the
set of words they accept. A language accepted by some DFA is called a *regular* language.

Every lanaguge defined by a DFA is also defined by a RegEx, although this fact is not formalized
in this project (or in the current state of Mathlib).

In lean, a DFA is a structure that takes two types as input:
  - `α` is the type of the alphabet
  - `σ` is the type of the states. This can be any type, even one with infinite elements. Thus,
  the name "DFA" is a bit of a misnomer, and to make a true DFA we must have some assumption that
  `σ` is a finite type.

This structure has three fields:
  - a transition function `step : σ → α → σ`
  - a starting state `start : σ`
  - a set of accepting states `accept : Set σ`

Here is what that definition looks like in Lean:

```
structure DFA (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Set σ
```

### Running a DFA

Given a DFA `M : DFA α σ`, we can "run" it on a word starting from any state. The function `evalFrom`
takes a starting state and a word (list of alphabet symbols) and returns the final state
reached after processing the entire word:

```
-- `evalFrom M s w` runs the DFA `M` on word `w` starting from state `s`,
-- returning the final state reached.
def evalFrom (M : DFA α σ) (s : σ) : List α → σ := List.foldl M.step s

-- `eval M w` runs the DFA on word `w` starting from the start state.
def eval (M : DFA α σ) : List α → σ := M.evalFrom M.start
```

To determine whether a DFA accepts a word, we check if the final state is in the accept set:

```
-- `acceptsFrom M s w` is true iff the DFA accepts word `w` when starting from state `s`.
def acceptsFrom (M : DFA α σ) (s : σ) (w : List α) : Prop := M.evalFrom s w ∈ M.accept

-- The language accepted by a DFA is the set of words it accepts from the start state.
def accepts (M : DFA α σ) : Language α := { w | M.acceptsFrom M.start w }
```

## DFA morphisms

All of the definitions above are from Mathlib, but this project build upon them with a notion
of DFA morphisms.

A DFA morphism is a function between the state-types of two DFAs that preserves the
start state, accept states, and the transition function.

This is implemented as a structure that takes two DFAs as input (they must be defined over the
same alphabet), and has 4 fields. The first field, `toFun` is the underlying function between
the state types, while the other 3 fields are PROOFS that that function perservies certain
properties.

Here is what that definition looks like in lean:

```
-- A morphism of DFAs from `M` to `N`.
structure Hom (M : DFA α σ₁) (N : DFA α σ₂) where
  toFun : σ₁ → σ₂                            -- Underlying function map
  map_start : toFun M.start = N.start        -- Preserves the start state.
  map_accept (q : σ₁) : q ∈ M.accept ↔ toFun q ∈ N.accept  -- Preserves accept states.
  map_step (q : σ₁) (w : List α) :           -- Preserves state transitions.
    toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

-- `M →ₗ N` denotes the type of morphisms from the DFA `M` to the DFA `N`.
infixr:25 " →ₗ " => Hom
```

### Morphisms Preserve Language

We prove that DFA morphisms preserve the accepted language of a DFA. That is, if there exists
some morphism from DFA `M` to DFA `N`, then both DFAs accept the same language.

Proof:
Let `f : M →ₗ N` be a morphism of DFAs, we claim that `M.accepts = N.accepts`
It is sufficient to show that, for all words `w : List α`, `w ∈ M.accepts ↔ w ∈ N.accepts`
Forward direction: assume `w ∈ M.accepts` and `M.eval w ∈ M.accept`
Because `f` preserves accepting states, we have `f (M.eval w) ∈ N.accepts`.
Because `f` preserves state transitions, `f (M.eval w) = N.evalFrom (f M.start) w`
Because `f` preserves starting states, `f M.start = N.start`.
Thus, `N.evalFrom N.start w ∈ N.accept` and `w ∈ N.accept`
The backward direction holds by a similar argument.

Here is what that proof looks like in lean:

```
-- A morphism of DFAs preserves the accepted language.
theorem Hom.pres_lang {M : DFA α σ₁} {N : DFA α σ₂} (f : M →ₗ N) :
    M.accepts = N.accepts := by
  -- Two languages are equal iff they contain the same words
  ext w
  -- Unfold the definition of `accepts`
  simp only [accepts, acceptsFrom, Set.mem_setOf_eq]
  constructor
  -- Forward direction: M accepts w → N accepts w
  · intro h  -- `h : M accepts w` is now a local variable, and the goal is `N accepts w`
    rw [f.map_accept] at h    -- Use `map_accept` to rewrite `h`
    rw [f.map_step M.start w] at h
    rw [f.map_start] at h
    exact h
  -- Backward direction: N accepts w → M accepts w
  · intro h
    rw [f.map_accept, f.map_step M.start w, f.map_start]
    exact h
```

We say a DFA morphism is *surjective* iff its underlying function is surjective, notated `M ↠ N`.

An *equivalence* of DFAs is a bijective morphism, notated `M ≃ₗ N`.

## What is DFA Minimization?

Many DFAs can define the same language. Consider the following example:

### Example: Two DFAs for "ends with 'a'"

We define two DFAs that define the language of all strings over the alphabet `{a, b}` that end
with `a`.

**A minimal two-state DFA:**
- State `q0`: Haven't seen 'a' as the last character (starting state)
- State `q1`: Last character was 'a' (accepting state)
- Transitions: On 'a', go to `q1`. On 'b' (1), go to `q0`.

**A three-state DFA with a redundant state:**
- States `q0`, `q1` as above, plus a `dead` state
- The `dead` state transitions only to itself
- No transitions lead into the `dead` state
- This DFA accepts the same language but has an unnecessary state

Both DFAs accept exactly the strings ending with 'a', but the first is minimal.

### Minimality via Preorder

DFA minimization is the process of finding the smallest DFA that accepts a particular language.

The obvious definition of "smallest" is the DFA with the fewest number of states, but there is
a stricter definition of minimality that is used in automata theory, based minimality in terms
of a preorder defined on DFAs over the same alphabet.

This preorder is defined as follows: `M ≤ N` iff there exists a surjective DFA morphism
from `N` to `M` (`N ↠ M`).

The minimal DFA for a language `L` is the unique (up to equivalence) DFA `M` that is minimal
in this preorder.

In this project, we formalize this definition of minimality and we construct and algorithm
that, given a DFA `N` that accepts a language `L`, constructs the minimal DFA `M` for `L`.
Additionally, we prove that `M` is unique up to equivalence.

## The Minimization Algorithm

There are a few different algorithms for minimizing DFAs.

TODO: Refrence the name of this algorithm from the Hopcroft textbook

It is based on collapsing states of the DFA that are equivalent in terms of the language they
accept. More precisely, we define an equivalence relation on the states called the
*Nerode Equivalence*. Two states `q₁` and `q₂` are Nerode equivalent iff for every word `w`,
the DFA accepts `w` when starting from `q₁` iff it accepts `w` when starting from `q₂`.

We can then define the minimal DFA as the DFA whose states are the equivalence classes of this
relation, with the transition function, start state, and accept states defined in the obvious way.

```
-- For a DFA `M`, `M.toNerodeDFA` is a DFA whose state-space is the
-- quotient of `M`'s by the nerode Equivalence.
def toNerodeDFA :
    DFA α (Quotient (M.nerodeEquiv)) where
  step (s' : Quotient (M.nerodeEquiv)) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerodeEquiv.step; apply h) s'
  start := ⟦M.start⟧
  accept := {⟦q⟧ | q ∈ M.accept }
```

However, one subtlety is that this will only actually produce a minimal DFA if the original
DFA is *accessible*, meaning that every state is reachable from the start state. Otherwise,
there will be unreachable "dead" states whose equivalence classes will still be present in
the quotient.

Thus, the acutal minimization algorithm first removes innaccessible states, then constructs
the Nerode DFA. We define a function `toAccessible` that removes innaccessible states from
a DFA.

```
-- Given a `M : DFA α σ`, `M.toAccessible` is `M` but with all
-- the non-accessible states removed.
def toAccessible : DFA α {s // M.IsAccessibleState s} where
  step s a := ⟨M.step s.val a, by
    obtain ⟨x, hx⟩ := s.prop
    use x ++ [a]
    simp [hx]⟩
  start := ⟨M.start, by use []; simp⟩
  accept := {s | s.val ∈ M.accept}
```

Now, we can define the minimization function as the composition of these two functions.

```
-- The minimal DFA accepting the same language as `M`
def minimize : DFA α (Quotient (M.toAccessible.nerodeEquiv)) :=
  M.toAccessible.toNerodeDFA
```

## Computablity

Lean formalizations are often *non-computable*, meaning that they define mathmatical objects
and functions over them in such a way that can be reasoned about but not actually executed to
produce concrete results.

In fact, the definition of a DFA in Mathlib is not sufficiant to actually *run* a DFA on an
input string, and test if it accepts or rejects it. The state type `σ` is completely
unconstrained, so there is not automatically any procedure for testing if two states
(elements of type `σ`) are equal, or if they are in the set of accepting states (a `Set σ`).

Much of the work of this project is devoted to providing *computable* versions of the
definitions of DFAs and algorithms on them, such that the DFAs can actually be exectued on
input strings, and such that the minimization algorithm can actually produce a computable
minimal DFA if given a computable DFA as input.

In fact, much of the mathmatical content of the project only comes up in the computable
setting.

For example, the `toAccessible` function from earlier is non-computable unless we define an
algorithm for actually deciding, in a provably finite amount of steps, wheather a state is
accessible or not.

We call this predicate on states `IsAccessibleState`, and it can be non-computabley defined
as follows:

```
-- A predicate on States of a `DFA` asserting that there exists a word
-- `w` such that `M.eval w` equals that state
def IsAccessibleState (s : σ) : Prop :=
  ∃ w : List α, M.eval w = s
```

To make this predicate computable, we have to provide a version that is a function from
states to booleans (true or false), rather than to the `Prop` type.

In lean, all functions must be provably terminating, so to define such a function, we cannot
simply search over the infinite set of all words over the alphabet `α` to see if any of them
access the state `s`. So, we prove that if a state is accessible, then it is accessed by some
word of length less than or equal to the number of states in the DFA.

```
-- Given that the set of states is finite, every accessible state is reachable by a
-- word of length at most the number of states.
theorem exists_short_access_word (s : σ) {w : List α}
    (hw : M.eval w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ M.eval v = s := by
  -- Strong recursion on the length of `w`
  -- Use Mathlib's `DFA.evalFrom_split` lemma to split `w` into `a ++ b ++ c`
  -- with a loop on `b`, allowing us to remove the loop and get a shorter word.
  ...
```

Using this lemma, we can define a decidable version of `IsAccessibleState` by checking only
the finite set of words of length less than or equal to the number of states.

### The `Fin` Typeclass

This project defines a custom typeclass `Fin M` for DFAs whose set of accepting states is a
`Finset` rather than simply a `Set`. This allows for boolean valued functions that test
if a given state is in the set of accepting states, so long as we also have a `DecidableEq`
instance on the type of states.

```
-- A typeclass for DFAs with a computable finite set of accepting states.
class Fin (M : DFA α σ) where
  finAccept : Finset σ              -- The accepting states as a `Finset`.
  accept_eq : ↑finAccept = M.accept -- The `Finset` equals the accept `Set`.
```

Without an instance of `Fin M` on a DFA `M`, it would be impossible to computably determine
if an arbitrary word is accepted by `M`.

## Computable Nerode Equivalence

To make to `toNerodeDFA` (state collapsing) function computable, we need a boolean-valued function
for testing if two states are Nerode equivalent.

Here is a prop-valued definition of this relation:

```
def NerodeEquivalence (s₁ s₂ : σ) : Prop := M.acceptsFrom s₁ = M.acceptsFrom s₂
```

This states that two states are nerode equivalent iff they accept the same language when
starting from those states.

However, these languages are sets of words, which are infinite in general, so we cannot
simply check if these two sets are equal decidably.

To make this relation computable, use the fact that two states are Nerode equivalent iff for
every word `w` of length less than or equal to the number of states, both states either
accept or reject `w`.

We can now decide the Nerode equivalence relation by checking this finite set of words.

The proof of the theorem above is the most involved proof in this project, and it involves
defining a bounded version of the Nerode equaivalence relation and proving several lemmas
about it.

## Bounded Nerode Equivalence

We say two states `s₁` and `s₂` are *k-bounded Nerode equivalent* iff for every word `w` of
length less than or equal to `k`, both states either accept or reject `w`.

It is obvious that if two states are Nerode equivalent, then they are k-bounded Nerode
equivalent for every `k`. The converse is also true, which is the key insight that allows us
to decide Nerode equivalence.

### Bounded Nerode Monotonicity

It is also clear that if two states are k-bounded Nerode equivalent, then they are j-bounded
Nerode equivalent for all `j ≤ k`.

### Bounded Nerode Stabilization

The key insight is that the bounded Nerode equivalence relation stabilizes at `k = |σ|`.
That is, if two states are Nerode equivalent up to words of length `|σ|` (the number of
states in the DFA), then they are Nerode equivalent for words of all lengths. Proving this
theorem allows us to decide Nerode equivalence.

To prove this theorem, we use a lemma that if the bounded Nerode equivalence at `k` is the
same relation as the bounded nerode equivalence at `k+1`, then the relation has stabilized,
and thus equals the full Nerode equivalence relation.

For each increase in `k`, the number of equivalence classes can only increase, by
monotonicity. If the number of equavilance classes of `k` equales the number of equivalence
classes of `k+1`, then the relations must be the same (this is a general property of
monotonic relations), and thus by the lemma above, the relation has stabilized.

Note that the bounded Nerode equivalence relation at `k = 0` only depends on wheather the
state is an accepting state or not, and thus there are at most two equivalence classes for
this relation.

We can now say that, for each increase in `k`, the number of equivalence classes *strictly*
increases, or it stabilizes into the full nerode equivalence. Thus, the bounded nerode
relation at `k` either has at least `k + 1` equivalence classes, or it is the full nerode
equivalence relation.

Becuase an equivalence relation on a finite set cannot have more equivalence classes than
the size of the set, we have that at `k = |σ|`, the bounded nerode equivalence relation must
have stabilized into the full nerode equivalence relation.

## Connection to left quotients and the "nerode automaton" of a language

The *left-quotient* of a language `L` by a word `w` is the language consisting of all words
`v` such that `w ++ v ∈ L`.

Given a DFA `M` that accepts a language `L`, the left-quotient of `L` by a word `w` is
exactly the language accepted from the state `M.eval w`.

Using this fact, we can construct a (not necessarly finite) deterministic automaton that
accepts an arbitrary langage `L` by taking the states to be the left-quotients of `L` by all
words `w`, with the start state being `L`, the accept states being those left-quotients that
contain the empty word, and the transition function mapping languages to their left-quotient
by a single letter.

When the set of left-quotients of a language is finite, this construction produces a
(actually-finite) DFA that accepts the language, and this is in fact the minimal DFA for
the langauge.

Mathlib already contains this constuction, called `Language.toDFA`.

```
-- The left quotients of a language are the states of an automaton that accepts the language.
def toDFA : DFA α (Set.range L.leftQuotient) where
  step s a := by
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [← hy, leftQuotient_append]
  start := ⟨L, by exists []⟩
  accept := { s | [] ∈ s.val }
```

This function differes from this project's minimization algorithm in that it starts from an
arbirtrary *language* rather than a DFA. As such, it is not able to produce *computable* or
*finite* DFAs.

Unlike this project's algorithm, The DFAs returned by `language.toDFA` cannot be executed on
input strings, nor is there any proof that the returned DFA is acutally finite.

However, we prove that, given a DFA `M` that accepts a language `L`, the DFA produced by
`L.toDFA` is *equivalent* (in the bijective DFA morphism sense) to `M.minimize`.

## Project Structure

The formalization is organized as follows:

- `MyProject/DFA/Hom.lean` — DFA morphisms, surjections, equivalences, and the preorder on DFAs
- `MyProject/DFA/Accessible.lean` — Accessibility predicate, `toAccessible`, and decidability
- `MyProject/DFA/Nerode.lean` — Nerode equivalence, bounded equivalence, and stabilization proofs
- `MyProject/DFA/Minimize.lean` — The minimization algorithm and correctness proofs
- `MyProject/DFA/Fin.lean` — The `Fin` typeclass for computable DFAs

## Current Developments

I initially intended for this project to be a contribution to Mathlib, and
I recently made a post on the Lean 4 Zulip channel about this project.
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Automata.20Theory.20Contribution/with/562817136

However, they pointed me to another community project called `CSLib`, which focuses more on
automata theory. This project uses different definitions of DFAs, but like mathlib it lacks a
formalization of DFA morphisms, accessibility, and minimization. I am currently working on
refactoring this project to use these new definitions and making a pull request to CSLib.

## TODO

Refrence textbooks (Hopcroft and Ullman's "Introduction to Automata Theory")
-/
