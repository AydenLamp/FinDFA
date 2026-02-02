# Formalization of DFA Minimization in Lean 4

This repository contains a formalization of the minimization of deterministic finite automata (DFAs) in the Lean 4 theorem prover.

# Why Formalize Mathmatics

Mathematics is typically communicated in precise but informal language, where definitions and proofs are written for human readers and leave many steps implicit. This style has proven powerful, but it also has a limitation: the correctness of a proof ultimately depends on social verification. Mathematicians check arguments themselves, discover errors, and fill in gaps. As proofs grow larger and more complex, this informal process becomes fragile.

Mathematicians responded to this problem with mathematical formalization, where definitions, statements, and proofs are represented inside a formal system with precise syntax and semantics. In a formal setting, a theorem is a syntactic object: a derivation from axioms and previously proved results, where every step is justified by an explicit rule. This yields a notion of proof that is not mediated by interpretation, but by a mechanical and machine-checkable standard. Instead of relying on “it is clear that…”, a formal proof must make every dependency explicit, sometimes at the cost of verbosity, but in exchange for guaranteed correctness.

Historically, fully formal proofs were too labor-intensive to be a realistic replacement for ordinary mathematical writing. This is the problem that interactive theorem provers (ITPs) were created to solve. An ITP is software in which a user incrementally constructs a proof while the system checks that each step follows from the axioms and inference rules of the underlying logic. Modern provers provide powerful automation high-level tactics so that users can write proofs at a reasonably high level of abstraction. At the same time, they are engineered around a trusted kernel which checks proofs, and everything else is treated as a convenience layer whose output is still validated by the kernel.

## Lean 4 and Mathlib

Lean 4 is a modern proof assistant that is both an ITP and a functional programming language based on dependent type theory. This combination is particularly well suited to formalizing mathematics that has an algorithmic component. In Lean, one can define mathematical objects, state theorems about them, and also write executable functions that compute with them. A proof about an algorithm can therefore refer to the actual definition being executed, not to an informal description that might subtly diverge from an implementation.

Large-scale formalization is made feasible by Lean’s community library, mathlib. Mathlib provides a broad foundation of definitions and theorems across many mathematical domains. In traditional mathematics, large projects are limited by the amount of trust required between collaborators—each participant must rely on the correctness of others’ work. In a formal library, contributions are checked by the kernel, so the “cost of trust” is reduced. This enables thousands of contributors to build a coherent, machine-checked body of mathematics that future work can extend.

## Machine checked algorithms

An application of proof assistants is the verification of algorithms against mathematical specifications. In an ITP like Lean, one can define a specification of correctness, define an algorithm as a function, then prove that the algorithm satisfies the specification for all inputs. This allows one to verify that an algiorithm is not only correct, but also satifies stonger properties such as always producing a canonical result (if you define some notion of equivalence). 

## Computability 

Formal verification also brings the relationship between mathematics and computation into view. In traditional classical mathematics, it is common to prove that an object exists without giving a procedure to construct it. In contrast, in constructive mathematics, an existence proof is expected to provide a method of construction. Proof assistants make this distinction concrete because definitions can be executed and theorems can carry computational content.
Lean enforces that definitional computation is well behaved: functions are total (they must terminate) and deterministic (the same input produces the same output). As a result, implementing an algorithm that constructs an object can be viewed as giving computational evidence of existence. When paired with a proof of correctness, the algorithm becomes a constructive witness: not only does a desired object exist, but we can acutally compute it. 

## Table of Contents

- [What is Lean?](#what-is-lean)
- [What is Mathlib?](#what-is-mathlib)
- [Motivation](#motivation)
- [What is a DFA?](#what-is-a-dfa)
- [Minimal DFAs](#minimal-dfas)
- [DFA Morphisms](#dfa-morphisms)
- [Computability](#computability)
- [Project Structure](#project-structure)
- [Current Developments](#current-developments)

---

## What is Lean?

Lean 4 is an interactive theorem prover (ITP) and programming language.

Unlike traditional programming languages, Lean is functional and based on dependent type theory, which allows types to depend on values. This enables Lean to serve both as a programming language and a proof assistant.

Lean uses the Curry–Howard correspondence, where some types are interpreted as propositions, and terms of those types are interpreted as proofs.

Lean stands out among ITPs for its focus on formalizing mathematics and its strong community tooling.

---

## What is Mathlib?

Mathlib is the mathematical library for Lean, containing over 1.5 million lines of formalized mathematics. It is the largest unified mathematical library for any theorem prover. It covers algebra, analysis, number theory, and a small amount of automata theory.

---

## Motivation

Mathlib already contains a definition of DFAs and some basic theorems about them (such as the pumping lemma), but it does not contain definitions or theorems related to DFA accessibility, morphisms, or minimization.

This project aims to fill that gap by providing a formalization of these concepts.

---

## What is a DFA?

A **deterministic finite automaton** (DFA) is a finite-state machine that accepts or rejects a given string of symbols by running through a sequence of states.

Every DFA is defined over a finite **alphabet**, which is a set of letters. When evaluated on a word over this alphabet, the DFA either accepts or rejects that word.

The figure below is a state diagram of a particular DFA defined over the alphabet {a, b}:

*[Insert Figure 1]*

This DFA has two states, labeled S₁ and S₂. The unlabeled arrow pointing to S₁ indicates that it is the **start state**, and the double circle around S₂ indicates that it is an **accepting state**. The labeled arrows are **state transitions**, and it is required that every state has exactly one outgoing arrow for each character in the alphabet.

When evaluating a word, a DFA begins at the designated start state, then follows the arrow labeled by the first letter of the word. Then, it follows the arrow labeled by the second letter of the word, and so on until you reach the end of the word. If the state it ends on is an accepting state, then the DFA accepts the word; otherwise, it rejects.

For example, evaluating the word "bab" on the DFA above:
1. Begin in state S₁
2. Read "b" → transition to S₁
3. Read "a" → transition to S₂
4. Read "b" → transition to S₂

Since S₂ is an accepting state, this DFA accepts the word "bab".

The set of words that a DFA accepts is called the **language** of that DFA.

You might notice that the language of this DFA is the set of all words that contain an odd number of "a"s (and any number of "b"s).

### Lean Definition

Mathlib contains a formal definition of a DFA as a structure type:

```lean
structure DFA (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Set σ
```

This structure is parameterized by two input types, `α` and `σ`, which represent the alphabet and set of states, respectively. It has three fields:
- `step : σ → α → σ` — the transition function, which encodes the "arrows" between states
- `start : σ` — a single designated start state
- `accept : Set σ` — a set of accepting states

Mathlib also defines DFA evaluation as follows:

```lean
/-- `M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`. -/
def evalFrom (M : DFA α σ) (s : σ) : List α → σ :=
  List.foldl M.step s

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval (M : DFA α σ) : List α → σ :=
  M.evalFrom M.start
```

Mathlib provides a function that returns the language accepted by a DFA from a particular state. Here, `Language α` is just a wrapper for `Set (List α)`:

```lean
/-- `M.acceptsFrom s` is the language of `x` such that `M.evalFrom s x` is an accept state. -/
def acceptsFrom (s : σ) : Language α := {x | M.evalFrom s x ∈ M.accept}

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : Language α := M.acceptsFrom M.start
```

Let's test out some of these functions on our simple DFA from Figure 1. First, we define the state and alphabet types:

```lean
inductive α₁ : Type
  | a
  | b
deriving DecidableEq, Fintype

inductive σ₁ : Type
  | s₁
  | s₂
deriving DecidableEq, Fintype
```

Now, we can define our DFA from Figure 1 over these types:

```lean
def M₁ : DFA α₁ σ₁ where
  step (s : σ₁) (x : α₁) :=
    match s, x with
    | σ₁.s₁, α₁.a => σ₁.s₂  -- (s₁, a) goes to s₂
    | σ₁.s₁, α₁.b => σ₁.s₁  -- loop on b in s₁
    | σ₁.s₂, α₁.a => σ₁.s₁  -- (s₂, a) goes to s₁
    | σ₁.s₂, α₁.b => σ₁.s₂  -- loop on b in s₂
  start := σ₁.s₁
  accept := {σ₁.s₂}
```

We can use Lean's `#eval` to see the result of evaluating the word "bab" on this DFA:

```lean
#eval M₁.eval [α₁.b, α₁.a, α₁.b]
```

This prints `σ₁.s₂` to the Infoview, which is an accepting state.

### Another DFA Example

For a slightly more complex example, consider this DFA, again defined over the alphabet {a, b}:

*[Insert Figure 2]*

The language of this DFA is the set of all words with an odd number of "a"s *and* an odd number of "b"s.

Now, imagine that you are halfway through evaluating a word for this DFA, and you are currently at state S₂. What does the rest of the word have to look like for the whole word to be accepted? The rest of the word must contain an even number of "a"s and an odd number of "b"s.

| State | Required suffix language |
|-------|--------------------------|
| S₁ | Odd "a"s and odd "b"s |
| S₂ | Even "a"s and odd "b"s |
| S₃ | Odd "a"s and even "b"s |
| S₄ *(accepting)* | Even "a"s and even "b"s |

This idea of the language accepted *from a particular state* is fundamental in algorithms that minimize DFAs.

---

## Minimal DFAs

Multiple DFAs can accept the same language. For example, here is another DFA that also accepts the language of words with an odd number of "a"s and an odd number of "b"s:

*[Insert Figure 3]*

Given a DFA, one may ask if this DFA is **minimal** for the language it accepts. For now, let's call a DFA "minimal" if it has the fewest states of all DFAs recognizing the same language. Later, we will define a stronger notion of minimality based on DFA morphisms.

This DFA is not minimal, and this can be illustrated by considering the language accepted from each state:

| State | Required suffix language |
|-------|--------------------------|
| S₁ or S₅ | Odd "a"s and odd "b"s |
| S₂ or S₆ | Even "a"s and odd "b"s |
| S₃ or S₇ | Odd "a"s and even "b"s |
| S₄ or S₈ *(accepting)* | Even "a"s and even "b"s |

When the language accepted from two states is the same (for example, S₁ and S₅), the DFA is not minimal because those states could be collapsed into a single state. Conversely, if the language accepted from each state is unique, as in Figure 2, the DFA is minimal.

### A Minimization Algorithm

DFA minimization is the problem of, given a DFA, creating a minimal DFA that accepts the same language.

We will minimize the DFA in Figure 3, again considering the languages accepted from each state (see table above).

We create a relation on the states of Figure 3 called the **Nerode equivalence**. Two states are Nerode-equivalent if and only if the language accepted from each state is the same. In this case:
- States S₁ and S₅ are Nerode-equivalent
- States S₂ and S₆ are Nerode-equivalent
- States S₃ and S₇ are Nerode-equivalent
- States S₄ and S₈ are Nerode-equivalent

```lean
def nerodeEquiv (M : DFA α σ) (s₁ s₂ : σ) : Prop :=
  M.acceptsFrom s₁ = M.acceptsFrom s₂
```

In our minimized DFA, the set of states will be the set of equivalence classes of the Nerode equivalence relation. In this case, we have four equivalence classes:
- {S₁, S₅}
- {S₂, S₆}
- {S₃, S₇}
- {S₄, S₈}

```lean
/-- For a DFA `M`, `M.toNerodeDFA` is a DFA whose state-space is the
quotient of `M`'s by the Nerode equivalence. -/
def toNerodeDFA (M : DFA α σ) : DFA α (Quotient M.nerodeEquiv) where
  step (s' : Quotient M.nerodeEquiv) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerodeEquiv.step; apply h) s'
  start := ⟦M.start⟧
  accept := {⟦q⟧ | q ∈ M.accept}
```

We designate the start state as the Nerode equivalence class containing the original start state (in this case, {S₁, S₅}), and we designate the accepting states as any Nerode equivalence classes containing an accepting state (in this case, {S₄, S₈}).

Notice how, if you are in state S₁ or S₅, seeing an "a" will always map to state S₂ or S₆. Seeing a "b" will always map to state S₃ or S₇. In fact, members of a Nerode equivalence class always transition to the same Nerode equivalence class on the same input. In this way, we say that the Nerode equivalence **preserves the transition function**. Because of this, we can define the transition function of the minimized DFA:

| State | Letter | Destination |
|-------|--------|-------------|
| {S₁, S₅} *(start)* | a | {S₂, S₆} |
| {S₁, S₅} | b | {S₃, S₇} |
| {S₂, S₆} | a | {S₁, S₅} |
| {S₂, S₆} | b | {S₄, S₈} *(accept)* |
| {S₃, S₇} | a | {S₄, S₈} *(accept)* |
| {S₃, S₇} | b | {S₁, S₅} |

Here is the resulting minimal automaton—notice how it is the same as the DFA in Figure 2:

*[Insert Figure 4]*

### A Problem with the Minimization Algorithm

The algorithm above often provides a minimal automaton, but only if the starting DFA is **accessible**.

A state of a DFA is **accessible** if there is some word that reaches that state. A DFA is **accessible** if every state is accessible.

```lean
/-- A predicate on states of a `DFA` asserting that there exists a word
`w` such that `M.eval w` equals that state. -/
def IsAccessibleState (M : DFA α σ) (s : σ) : Prop :=
  ∃ w : List α, M.eval w = s

/-- A typeclass on `DFA`s asserting that every state is accessible. -/
class Accessible (M : DFA α σ) where
  allAccessible (s : σ) : M.IsAccessibleState s
```

For example, consider this DFA, again accepting the language of words with odd "a"s and odd "b"s, but with an inaccessible state S₅:

*[Insert Figure 5]*

The language accepted from state S₅ is unique: any number of "b"s, followed by one "a", followed by an even number of "a"s and an even number of "b"s.

This adds another Nerode equivalence class, so the algorithm above would not fully minimize the DFA.

To reconcile this, we can update our minimization algorithm to trim away inaccessible states before (or after) collapsing Nerode-equivalent states:

```lean
/-- Given a `M : DFA α σ`, `M.toAccessible` is `M` but with all
the non-accessible states removed. -/
def toAccessible (M : DFA α σ) : DFA α {s // M.IsAccessibleState s} where
  step s a := ⟨M.step s.val a, by
    obtain ⟨x, hx⟩ := s.prop
    use x ++ [a]
    simp [hx]⟩
  start := ⟨M.start, by use []; simp⟩
  accept := {s | s.val ∈ M.accept}

/-- The minimal DFA accepting the same language as `M`. -/
@[simp] def minimize : DFA α (Quotient M.toAccessible.nerodeEquiv) :=
  M.toAccessible.toNerodeDFA
```

---

## DFA Morphisms

This project builds on the Mathlib implementation of DFAs with a notion of DFA morphisms.

A **DFA morphism** is a function between the state types of two DFAs that preserves the start state, accepting states, and the transition function.

In Lean, this is implemented as a structure parameterized by two DFAs (which must be defined over the same alphabet) with four fields. The first field, `toFun`, is the underlying function between the state types, while the other three fields are proofs that the function preserves the required structure.

We define notation such that `M →L N` is the type of morphisms from `M` to `N`:

```lean
structure Hom (M : DFA α σ₁) (N : DFA α σ₂) where
  toFun : σ₁ → σ₂
  map_start : toFun M.start = N.start
  map_accept : ∀ q : σ₁, (q ∈ M.accept) ↔ (toFun q ∈ N.accept)
  map_step : ∀ (q : σ₁) (w : List α),
    toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

infixr:25 " →L " => Hom
```

We prove in `Hom.pres_lang` that DFA morphisms preserve the accepted language. That is, if there exists a morphism from a DFA `M` to a DFA `N`, then `M` and `N` accept the same language.

We say that a DFA morphism is **surjective** if and only if its underlying function is surjective.

An **equivalence of DFAs** is a bijective morphism, notated `M ≃L N`.

### Minimality via Morphisms

Using this notion of DFA equivalence, we can define a more precise specification of DFA minimality.

We define a preorder on DFAs that are defined over the same alphabet:

```lean
/-- `M ≤ N` iff there is a surjective morphism `N ↠ M`. -/
def AccessibleLE (M : DFA α σ₁) [Accessible M] (N : DFA α σ₂) [Accessible N] : Prop :=
  Nonempty (N ↠ M)
```

This captures the idea that `M ≤ N` if and only if there is some structure-preserving function that *collapses* the states of `N` to those of `M`.

A **minimal DFA**, then, is a DFA that is minimal in this order:

```lean
/-- An accessible DFA is minimal if every smaller accessible DFA is equivalent to it. -/
def IsMinimal (M : DFA α σ₁) [Accessible M] : Prop :=
  ∀ {σ₂ : Type*} (N : DFA α σ₂) [Accessible N] (_ : N ≤ M),
    Nonempty (M ≃ₗ N)
```

We prove that the DFA returned by our minimization algorithm is minimal:

```lean
/-- `M.minimize` is minimal by our partial order defined by the existence of surjective
DFA morphisms. -/
theorem minimize_isMinimal : M.minimize.IsMinimal := by
  exact M.toAccessible.toNerodeDFA_isMinimal
```

---

## Computability

The formalization presented above is not sufficient to actually *compute* a minimal DFA. We defined the Nerode equivalence as a proposition, but what we want is a function `state → state → Bool` that actually computes, in a finite amount of time, whether two states are Nerode-equivalent. Similarly, we need a function that *decides* if a state is accessible, rather than simply defining what an accessible state is propositionally.

Writing these computable functions, and proving that they are correct, makes up the bulk of this project. In fact, much of the mathematical content of DFA minimization only becomes relevant in this computable setting.

### Computable Accessibility Algorithm

Recall the definition of an accessible state:

```lean
/-- A predicate on states of a `DFA` asserting that there exists a word
`w` such that `M.eval w` equals that state. -/
def IsAccessibleState (M : DFA α σ) (s : σ) : Prop :=
  ∃ w : List α, M.eval w = s
```

The set of words over the alphabet is infinite, so how does one test, in a finite amount of time, whether any of those words reaches the state? We make use of an important theorem:

> **Theorem:** If a state is accessible, then it is accessed by some word of length at most |σ| (the number of states).

```lean
/-- Given that the set of states is finite, every accessible state is reachable by a
word of length at most the number of states. -/
theorem exists_short_access_word (s : σ) {w : List α}
    (hw : M.eval w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ M.eval v = s := by
  ...
```

I will not explain the proof fully here, but it makes use of strong induction and the fact that, if a path through a DFA is longer than the number of states in the DFA, then there must be a repeated state in that path.

Using this theorem, we can now decide if a state is accessible by checking only the finite set of words of length at most |σ|.

### Computable Nerode Equivalence

To make the full minimization pipeline computable, we need a computable algorithm that decides if two states are Nerode-equivalent.

Recall that two states are Nerode-equivalent if and only if the languages accepted from those states are equal. We again have the problem that, in general, these languages are infinite sets of words, so we must use a theorem to reduce this to a finite check:

> **Theorem:** Two states are Nerode-equivalent if and only if, for all words of length at most |σ|, evaluating the word from those states leads to the same acceptance outcome.

The proof of this theorem is the most involved in the project. I will explain it here at a high level.

#### Bounded Nerode Equivalence

First, we formalize the notion of two states defining the same language for words up to some length *n*:

```lean
/-- A word indistinguishes two states if evaluating from them leads to the same acceptance
outcomes. -/
private def Indist (M : DFA α σ) (w : List α) (s₁ s₂ : σ) : Prop :=
  (M.evalFrom s₁ w ∈ M.accept) ↔ (M.evalFrom s₂ w ∈ M.accept)

/-- The bounded Nerode equivalence at level `n`: two states are equivalent if they are
indistinguishable by words of length ≤ `n`. -/
def boundedNerode (M : DFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, w.length ≤ n → M.Indist w s₁ s₂
```

We can now state our theorem as:

> Two states are Nerode-equivalent if and only if they are *n*-bounded-Nerode-equivalent for *n* = |σ|.

#### Monotonicity of Bounded Nerode Equivalence

In order to prove the above theorem, we establish that if *n* ≤ *m*, then if two states are *m*-bounded-Nerode-equivalent, they are also *n*-bounded-Nerode-equivalent:

```lean
/-- Monotonicity of bounded Nerode. -/
private theorem boundedNerode_mono {n m : ℕ} (hle : n ≤ m) :
    M.boundedNerode m ≤ M.boundedNerode n := by
  simp [Setoid.le_def, boundedNerode]
  intros s₁ s₂ h₁ w h₂
  apply h₁
  omega
```

This theorem also implies that the *n*-bounded-Nerode relation partitions the set of states into a number of equivalence classes that is increasing in *n*.

#### Stabilization of Bounded Nerode Equivalence

We say that the bounded Nerode equivalence **stabilizes** at *n* if *n*-bounded-Nerode-equivalence is the same relation as (*n* + 1)-bounded-Nerode-equivalence. We prove that if the bounded Nerode equivalence stabilizes at *n*, then it equals the bounded Nerode equivalence at *m* for all *m* ≥ *n*, and thus equals the unbounded Nerode equivalence:

```lean
/-- If bounded Nerode stabilizes at `n`, then it equals the Nerode equivalence. -/
private lemma boundedNerode_stable_eq_nerode {n : ℕ}
    (heq : M.boundedNerode n = M.boundedNerode (n + 1)) :
    M.boundedNerode n = M.nerodeEquiv := by
  ...
```

We can now say that, for any *n*, (*n* + 1)-bounded-Nerode-equivalence is either *strictly* finer than *n*-bounded-Nerode-equivalence (and thus partitions the set of states into *strictly* more equivalence classes), or it equals the full Nerode equivalence.

Because an equivalence relation cannot partition a set into more equivalence classes than there are elements in the set, the bounded Nerode equivalence at *n* = |σ| must be stabilized and thus equals the unbounded Nerode equivalence.

This allows us to decide if two states are Nerode-equivalent by checking only the finite set of words of length at most |σ|, making our relation computable:

```lean
/-- Decidability instance for testing if two states of a finite DFA are
Nerode-equivalent. -/
instance nerode_decidable : DecidableRel M.nerodeEquiv := by
  intros s₁ s₂
  apply decidable_of_decidable_of_iff (M.boundedNerode_iff_nerode s₁ s₂)
```

---

## Project Structure

The formalization is organized as follows:

| File | Contents |
|------|----------|
| `MyProject/DFA/Hom.lean` | DFA morphisms, surjections, equivalences, and the preorder on DFAs |
| `MyProject/DFA/Accessible.lean` | Accessibility predicate, `toAccessible`, and decidability |
| `MyProject/DFA/Nerode.lean` | Nerode equivalence, bounded equivalence, and stabilization proofs |
| `MyProject/DFA/Minimize.lean` | The minimization algorithm and correctness proofs |
| `MyProject/DFA/Fin.lean` | The `Fin` typeclass for computable DFAs |

---

## Current Developments

I initially intended for this project to be a contribution to Mathlib, and I recently made a post on the Lean 4 Zulip channel about it:

[Automata Theory Contribution – Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Automata.20Theory.20Contribution/with/562817136)

However, I was pointed to another community project called **CSLib**, which focuses more directly on automata theory. This project uses different definitions of DFAs, but (like Mathlib) it lacks a formalization of DFA morphisms, accessibility, and minimization. I am currently refactoring this project to use the CSLib definitions and preparing a pull request to CSLib.
