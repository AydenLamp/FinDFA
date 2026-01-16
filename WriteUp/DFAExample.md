# What is a DFA?

A **deterministic finite automaton** (DFA) is a finite-state machine that accepts or rejects a given string of symbols by running through a sequence of states.

Every DFA is defined over a finite **alphabet**, which is a set of letters. When evaluated on a word over this alphabet, the DFA either accepts or rejects that word.

The figure below is a state diagram of a particular DFA defined over the alphabet {a, b}

*insert ex.1*

This DFA has two states, labled S_1 and S_2. The unlabeled arrow pointing to S_1 indictes that it is the **start state**, and the circle around S_2 indicates that it is an **accepting state**. The labeled arrows are **state-transitions**, and it is requried that every state has exactly one outgoing arrow for each character in the alphabet. 

When evaluating a word, a DFA begins at the designated start state, then follows the arrow labeled by the first letter of the word. Then, it follows the arrow labeled by the second letter of the word, and so on until you reach the end of the word. If the state it ends on is an accepting state, then the DFA accepts the word; otherwise it rejects.

For example, evaluating the word "bab" on the DFA above, we begin in state S_1, then we read the first "b" and transition to state S_1, then we read "a" and transition to S_2, then we read the final "b" and transition to S_2. S_2 is accepting, so this DFA accepts the word "bab".

The set of words that a DFA accepts is called the **language** of that DFA. 

You might notice that the language of this DFA is the set of all words that contain an odd amount of "a"s, and any amount of "b"s.

TODO - Add a formal definition of DFAs from Lean?

For a slightly more complex example, consider this DFA, again defined over the alphabet {a, b}

*insert ex.2*

The language of this DFA is the set of all words with an odd amount of "a"s and an odd amount of "b"s. 

Now, imagine that you were halfway through evaluating a word for this DFA, and you are currently at state S_2. What does the rest of the word have to look like for the whole word to be accepted? The rest of the word must contain an even amount of "a"s and an odd amount of "b"s. 

*table 1*
What state are you at?  |  What do you need to accept?
S_1 | Odd "a"s and Odd "b"s
S_2 | Even "a"s and Odd "b"s
S_3 | Odd "a"s and Even "b"s
S_4 (accepting) | Even "a"s and Even "b"s

This idea of the language accepted *from a particular state* is fundemental in algorithms that minimize DFAs.

# Minimimal DFAs

Multiple DFAs can accept the same language. For example, here is another DFA that also accepts the language of words with an odd amount of "a"s and an odd amount of "b"s. 

*insert ex.3*

Given a DFA, one may ask if this DFA is **minimal** for the language it accepts. For now, lets call a DFA "minimal" if it has the least amount of states of all DFAs recognizing the same language. Later, we will define a stronger notion of minimality based on the idea of a DFA morphism.

This DFA is not minimal, and this can be illustrated by considering the language accepted from each of the states.

*table 2*
What state are you at? | What do you need to accept?
S_1 or S_5 | Odd "a"s and Odd "b"s
S_2 or S_6 | Even "a"s and Odd "b"s
S_3 or S_7 | Odd "a"s and Even "b"s
S_4 or S_8 (accepting) | Even "a"s and Even "b"s

When the language accepted from some two states is the same (for example S_1 and S_5), the DFA is not minimal, because those states could be collabesed into a single state. Inversly, if the language accepted from each state is unique, as in example 2, the DFA is minimal.

## A Minimization Algorithm

DFA minimization is the problem of, given a DFA, create a minimal DFA that accepts the same language. 

We will minimize the DFA in example 3, and we will again consider the languages accepted from each state (table 2). 

We create a relation on the states of example 3 called the **Nerode-equivalence*. Two states are Nerode-equivalent iff the language accepted from that state is the same. In this case, states S_1 and S_5 are Nerode-equivalent, as are states S_2 and S_6, states S_3 and S_7, and S_4 and S_8. 

In our minimized DFA, the set of states will actually be the set of equivalence classes of the Nerode-equivalence relation. In this case, we have four eq-classes: {S_1 and S_5, S_2 and S_6, S_3 and S_7, S_4 and S_8}

We designate the start state as the Nerode-equivalence class containing the original start state (in this case, {S_1 and S_5}), and we designate the accepting states as the Nerode-equivalence classes containg an accepting state (in this case, {S_4 and S_8}).

Notice how, if you are in state S_1 or S_5, seeing an "a" will always map to state S_2 or S_6. Seeing a "b" will always map to state S_3 or S_7. In fact, members of a Nerode-equivalence class always transition to the same Nerode-equivalence class on the same input. In this way, we say that the Nerode-equivalence **preserves the transition function**. Because of this, we can define the transition function of the minimized DFA:

*table 3*
State | Letter | Move to
{S_1 and S_5} (start) | a | {S_2 and S_6}
{S_1 and S_5} | b | {S_3 and S_7}
{S_2 and S_6} | a | {S_1 and S_5}
{S_2 and S_6} | b | {S_4 and S_8} (accept)
{S_3 and S_7} | a | {S_4 and S_8} (accept)
{S_3 and S_7} | b | {S_1 and S_5}

Here is the resulting minimal automaton, and notice how it is the same as the DFA in example 2. 

*insert example 4*

TODO - Show lean version of nerode collapsing algorithm

## A problem with the Minimization Algorithm

The algorithm above often provides a minimal automaton, but only if the starting DFA is **accessible**.

A state of a DFA is **accessible** if there is some word that reaches that state. A DFA is **accessible** if every state is accessible. 

For example, consider this DFA, again accepting the language of words with odd "a"s and odd "b"s, but with an inaccessible state S_5.

*insert example 5*

The language accepted from state 5 is unique: Any amount of "b"s, followed by one "a", followed by an even amount of "a"s and an even amount of "b"s. 

This adds another Nerode-equivalence class, thus the algorithm above would not minimize the DFA fully. 

To reconsile this, we can update our minimization algorithm to trim away inaccessible states before (or after) collapsing Nerode-equivalent states.

TODO - Show lean version of accesiblility trimming function

# Computability

The formilizatoin bits presented above are not sufficient to actually compute a minimal DFA. We defined the Nerode-equivalence as a proposition, but what we want is a function from state -> state -> Boolean that acually computes, in a finite amount of time, if two states are Nerode-equivalent or not. Symilarly, we need a function that decides if a state is accessible, rather than simply defining what an accessible state is propositionally.

Writing these computable functions, and proving that they are correct, make up the bulk of this project. In fact, much of the mathematical content of DFA minimization only becomes relevant in this computable setting. 

## Computable Accessiblity Algorithm

Recall the definition of an accessible state.

TODO - add lean code

The set of words over the alphabet is infitite, so how does one test, in a finite amount of time, if any of those words access the state? We make use of an important theorem:

If a state is accessible, then it is accessed by some word of length less than or equal to the number of states. 

TODO - add lean code

I will not explain the proof fully here, but it makes use of strong induction, and it uses the fact that, if a path through a DFA is longer than the amount of states in a DFA, then there must be a repeated state in that path.

Using this theorem, we can now decide if a state is accessible by checking only the finite set of words of length less than or equal to the amount of states.

## Computable Nerode-equivalence

To make the full minimization pipeline computable, we need a computable algorithm that decides if two states are Nerode-equivalent.

Recall that two states are Nerode-equivalent iff the languages accepted from those states are equal. We again have the problem that, in general, these languages are infintie sets of words, so we have to use a theorem to reduce this to a finite check:

Theorem: Two states are Nerode-equivalent iff, for all words of length less than or equal to the number of states, evaluating the word from those states leads to the same acceptance outcome.

The proof of this theorem is the most involved in the project, and I will explain it here at a high-level.

### Bounded-Nerode-equivalence

First we formalize the notion of two states defining the same language for words up to some length k. 

TODO- insert lean for k-bounded nerode eq

We can now state our theorem as: Two states are Nerode-equivalent iff they are k-bounded-Nerode-equivalent for k = |sigma| 

### Monotonicity of bounded-Nerode-equivalence

### Stabilization of bounded-Nerode-equivalence

# Connection to Left Quotients








