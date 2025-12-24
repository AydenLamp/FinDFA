# Lean Formalization of DFA Minimization

This repository contains a formalization of the minimization of deterministic finite automata (DFAs) in the Lean 4 theorem prover.

## What is Lean 4?

Lean 4 is an interactive theorem prover (ITP) and programming language.

Unlike traditional programming languages, Lean is *functional* and based on *dependent type theory*, which allows for types to depend on values. This enables Lean to serve both as a programming language and a proof assistant.

Lean uses the *Curry-Howard correspondence*, where some types are interpreted as propositions, and terms of those types are interpreted as proofs. 

Lean stands out among ITPs for its focus on formalizing mathematics and its strong community tooling. 

## What is Mathlib?

Mathlib is the mathematical library for Lean, containing over 1.5 million lines of formalized mathematics. It is the largest unified mathematical library for any theorem prover. It covers algebra, analysis, number theory, and a small amount of automata theory. 

## Motivation for the Project

Mathlib already contains a definition of DFAs and some basic theorems about them (such as the pumping lemma), but it does not contain definitions or theorems related to DFA accessibility, morphisms, or minimization.

This project aims to fill that gap by providing a formalization of these concepts.

# What is a DFA?

DFAs are machines that pattern match on strings. Defined on an *alphabet*, they either accept or reject words over that alphabet. In this way, they define a *language*, which is the set of words they accept. A language accepted by some DFA is called a *regular language*.

Every *regular language* is also defined by some regular expression, although this fact is not formalized in this project (nor in the current state of Mathlib).

## The Lean Definition of a DFA

In Lean, a DFA is a structure parameterized by an alphabet type (`α`) and a state type (`σ`). This structure has three fields: a transition function (`step : σ → α → σ`), a starting state (`start : σ`), and a set of accepting states (`accept : Set σ`). 

Here is what that definition looks like in Lean:

```lean
structure DFA (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Set σ
```

## Running a DFA

Given a DFA `M : DFA α σ`, we can run it on a word starting from any state. The function `evalFrom` takes a start state and a word (a list of alphabet symbols) and returns the final state reached after processing the entire word: 

```lean
def evalFrom (M : DFA α σ) (s : σ) : List α → σ :=
  List.foldl M.step s

def eval (M : DFA α σ) : List α → σ := 
  M.evalFrom M.start
```

To determine if a DFA accepts a word, we check whether the final state is a member of the set of accepting states `accept`:

```lean
def acceptsFrom (M : DFA α σ) (s : σ) (w : List α) : Prop := 
  M.evalFrom s w ∈ M.accept
```

We can now define the language of a DFA as the set of words accepted from the start state.

```lean
def accepts (M : DFA α σ) : Language α := 
  {w | M.acceptsFrom M.start w}
```

In Lean, the type `Set σ` is just a function from `σ → Prop`. 

Thus, for a DFA `M`, a state `s`, and a word `w`, `M.acceptsFrom s w` is a *proposition* that `M` accepts `w` from `s`, not a *boolean* (true or false). 

As such, there is no *decidable* procedure for determining if a word is accepted by a DFA. This means that, if one were to define a specific DFA in Lean, there would be no way to run that DFA on a specific word. 

This project defines a typeclass on DFAs called `Fin` that addresses this non-computability. 

## The `Fin` Typeclass

Given a DFA `M`, `Fin M` provides the set of accepting states `accept` as a `Finset` rather than a `Set`. The implementation of `Finset` in Lean is somewhat complicated, but what matters is that membership in a `Finset` can be *decided*, so long as we also have decidable equality on the underlying type. 

```lean
class Fin (M : DFA α σ) where
  finAccept : Finset σ
  accept_eq : finAccept.toSet = M.accept
```

# DFA Morphisms 

This project builds on the Mathlib implementation of DFAs with a notion of DFA morphisms.

A DFA morphism is a function between the state types of two DFAs that preserves the start state, accepting states, and the transition function.

In Lean, this is implemented as a structure that is parameterized by two DFAs (which must be defined over the same alphabet), and has four fields. The first field `toFun` is the underlying function between the state types, while the other three fields are proofs that the function preserves the required structure. 

We define notation such that `M →L N` is the type of morphisms from `M` to `N`. 

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

We say that a DFA morphism is *surjective* iff its underlying function is surjective.

An *equivalence* of DFAs is a bijective morphism, notated `M ≃L N`.

# DFA Minimization

Many DFAs can define the same language. DFA minimization is the process of finding the smallest DFA that accepts a given language. 

The standard automata-theory notion of "smallest" uses a preorder on DFAs:

`M ≤ N` iff there exists a surjective DFA morphism from `N` to `M`.

In this project, we formalize this definition and construct an algorithm that, given an input DFA, constructs the minimal DFA for the same language. We also prove that this DFA is unique up to equivalence. 

## The Minimization Algorithm

There are several DFA minimization algorithms, but this project uses one that is based on collapsing states that are equivalent in terms of the language they accept. More precisely, we define an equivalence relation on states called the *Nerode equivalence*. 

Two states `q₁` and `q₂` are Nerode equivalent iff, for every word `w`, the DFA accepts `w` from `q₁` iff it accepts `w` from `q₂`. 

The Lean implementation looks something like this:

```lean
def NerodeEquiv (M : DFA α σ) (s₁ s₂ : σ) : Prop := 
  M.acceptsFrom s₁ = M.acceptsFrom s₂
```

We then define a DFA whose states are equivalence classes of this relation. We call this the `NerodeDFA`, and it is nearly the minimal DFA (but it may have some inaccessible states).

```lean
def toNerodeDFA :
    DFA α (Quotient (M.nerodeEquiv)) where
  step (s' : Quotient (M.nerodeEquiv)) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerodeEquiv.step; apply h) s'
  start := ⟦M.start⟧
  accept := {⟦q⟧ | q ∈ M.accept}
```

## Accessibility

The `NerodeDFA` defined above yields a minimal DFA only if the original DFA is *accessible*, meaning every state is reachable from the start state by some word. Otherwise, unreachable states contribute unnecessary equivalence classes. 

The full minimization algorithm first removes inaccessible states, then constructs the Nerode quotient automaton. 

```lean
/-- A predicate on states of a `DFA` asserting that there exists a word
`w` such that `M.eval w` equals that state. -/
def IsAccessibleState (s : σ) : Prop :=
  ∃ w : List α, M.eval w = s

/-- Given a `M : DFA α σ`, `M.toAccessible` is `M` but with all
the non-accessible states removed. -/
def toAccessible : DFA α {s // M.IsAccessibleState s} where
  step s a := ⟨M.step s.val a, by
    obtain ⟨x, hx⟩ := s.prop
    use x ++ [a]
    simp [hx]⟩
  start := ⟨M.start, by use []; simp⟩
  accept := {s | s.val ∈ M.accept}

/-- The minimal DFA accepting the same language as `M`. -/
@[simp] def minimize : DFA α (Quotient (M.toAccessible.nerodeEquiv)) :=
  M.toAccessible.toNerodeDFA
```

# Computability 

Much of this project is devoted to providing computable variants of DFA definitions and algorithms.

We already discussed the `Fin` typeclass on DFAs above, which when combined with instances of the `Fintype` and `DecidableEq` typeclasses on the state and alphabet types, allows for deciding word membership in a DFA's language. 

We also define a *computable* version of the minimization algorithm, which preserves these typeclass instances. 

In fact, much of the mathematical content of this project only comes up in the finite and computable cases. 

For example, the `toAccessible` function described above is noncomputable unless we define an algorithm to *decide* if a given state is accessible. A key theorem is that if a state is accessible, then it is accessible by a word of length at most the number of states:

```lean
/-- Given that the set of states is finite, every accessible state is 
reachable by a word of length at most the number of states. -/
theorem exists_short_access_word (s : σ) {w : List α}
    (hw : M.eval w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ M.eval v = s := by
    ...
```

The proof proceeds by strong induction on the length of `w`, and we use Mathlib's `DFA.evalFrom_split` lemma to split `w` into `a ++ b ++ c` with a loop on `b`.

Using this theorem, we can define a decidable version of `IsAccessibleState` by checking only the finite set of words of length less than or equal to the number of states.

## Computable Nerode Equivalence

To make the `toNerodeDFA` quotient construction computable, we need a decidable procedure for testing if two states are Nerode-equivalent. 

Recall the proposition-valued definition:

```lean
def NerodeEquiv (M : DFA α σ) (s₁ s₂ : σ) : Prop := 
  M.acceptsFrom s₁ = M.acceptsFrom s₂
```

But `M.acceptsFrom s` is a language (generally an infinite set of words), so this equality is not decidable. 

The key idea is to use a bounded approximation: two states are Nerode equivalent iff they agree on all words of length at most the number of states. This reduces the test to a finite check. 

### Bounded Nerode Equivalence

We say two states are *k-bounded Nerode equivalent* iff for every word `w` of length at most `k`, both states either accept or reject `w`. 

The Lean implementation looks something like this:

```lean
def boundedNerode (M : DFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop := 
  ∀ w : List α, w.length ≤ n → 
    ((M.evalFrom s₁ w ∈ M.accept) ↔ (M.evalFrom s₂ w ∈ M.accept))
```

If two states are k-bounded equivalent, then they are j-bounded equivalent for all `j ≤ k`. 

```lean
/-- Monotonicity of bounded Nerode. -/
private theorem boundedNerode_mono {n m : ℕ} (hle : n ≤ m) :
    M.boundedNerode m ≤ M.boundedNerode n := by
  simp [Setoid.le_def, boundedNerode]
  intros s₁ s₂ h₁ w h₂
  apply h₁
  omega
```

We prove that the bounded Nerode equivalence relation *stabilizes* at `k = |σ|`. That is, if two states are Nerode equivalent up to words of length `|σ|` (the number of states in the DFA), then they are Nerode equivalent for words of all lengths. 

If the bounded Nerode equivalence at `k` is the same relation as the bounded Nerode equivalence at `k + 1`, then the relation has stabilized, and therefore agrees with the full (unbounded) Nerode relation. 

```lean
/-- If bounded Nerode stabilizes at `n`, then it equals the Nerode equivalence. -/
private lemma boundedNerode_stable_eq_nerode {n : ℕ}
  (heq : M.boundedNerode n = M.boundedNerode (n + 1)) :
    M.boundedNerode n = M.nerodeEquiv := by
  ...
```

As `k` increases, the bounded Nerode relation can only refine, by monotonicity. Equivalently, the number of equivalence classes can only increase as `k` increases. If the number of equivalence classes at `k` equals the number of equivalence classes at `k + 1`, then no refinement occurred, so the relations at `k` and `k + 1` must be identical. By the lemma above, this implies that the relation has stabilized. 

Note that the bounded Nerode equivalence at `k = 0` depends only on whether a state is accepting, since the only word of length 0 is the empty word. Thus, at `k = 0`, there are at most two equivalence classes. 

Therefore, for each increment of `k`, either the number of equivalence classes *strictly* increases, or the relation has stabilized into the full Nerode equivalence. In particular, the bounded Nerode relation at `k` either has at least `k + 1` equivalence classes, or it is already the full Nerode equivalence relation.

Because an equivalence relation on a finite set cannot have more equivalence classes than the size of the set, it follows that at `k = |σ|`, the bounded Nerode relation must have stabilized.

# Connection to Left Quotients 

The left quotient of a language `L` by a word `w` is the language consisting of all words `v` such that `w ++ v ∈ L`. 

Given a DFA `M` accepting `L`, the left quotient of `L` by `w` is exactly the language accepted from the state `M.eval w`.

Mathlib contains a construction (called `Language.toDFA`) that builds an automaton from an arbitrary language using left quotients.

This differs from this project's minimization algorithm because it starts from a language rather than a DFA and does not, by itself, provide computable or provably finite DFAs.

However, we prove that if a DFA `M` accepts a language `L`, then the DFA produced by `L.toDFA` is equivalent (in the bijective morphism sense) to `M.minimize`.

# Project Structure

The formalization is organized as follows:

- **MyProject/DFA/Hom.lean** — DFA morphisms, surjections, equivalences, and the preorder on DFAs
- **MyProject/DFA/Accessible.lean** — accessibility predicate, `toAccessible`, and decidability
- **MyProject/DFA/Nerode.lean** — Nerode equivalence, bounded equivalence, and stabilization proofs
- **MyProject/DFA/Minimize.lean** — the minimization algorithm and correctness proofs
- **MyProject/DFA/Fin.lean** — the `Fin` typeclass for computable DFAs

# Current Developments

I initially intended for this project to be a contribution to Mathlib, and I recently made a post on the Lean 4 Zulip channel about it:

https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Automata.20Theory.20Contribution/with/562817136

However, I was pointed to another community project called CSLib, which focuses more directly on automata theory. This project uses different definitions of DFAs, but (like Mathlib) it lacks a formalization of DFA morphisms, accessibility, and minimization. I am currently refactoring this project to use the CSLib definitions and preparing a pull request to CSLib.