# Code Formatting Guide

This document contains comprehensive code formatting guidelines for Lean 4 code and Mathlib contributions.

**Sources:**
* Lean Community website: <https://leanprover-community.github.io/index.html>
* Library Style Guidelines: <https://leanprover-community.github.io/contribute/style.html>

---

## Line Length

Lines must not be longer than **100 characters**.

---

## Hypotheses Placement

Generally, having arguments to the left of the colon is preferred over having arguments in universal quantifiers or implications, if the proof starts by introducing these variables.

**Preferred:**

```lean
example (n : ℝ) (h : 1 < n) : 0 < n := by linarith
```

**Not preferred:**

```lean
example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith
```

---

## Tactics

### Multiple Tactics on One Line

For single line tactic proofs (or short tactic proofs embedded in a term), it is acceptable to use `by tac1; tac2; tac3` with semicolons instead of a new line with indentation.

**General rule:** You should put a single tactic invocation per line, unless you are closing a goal with a proof that fits entirely on a single line.

**Acceptable exceptions:** Short sequences of tactics that correspond to a single mathematical idea can also be put on a single line, separated by semicolons:
- `cases bla; clear h`
- `induction n; simp`
- `rw [foo]; simp_rw [bar]`

Even in these scenarios, newlines are preferred.

### `simp` and `rw` Syntax

When using the tactics `rw` or `simp`, there should be a **space after the left arrow** `←`.

**Examples:**
- `rw [← add_comm a b]`
- `simp [← and_or_left]`

There should also be a space between the tactic name and its arguments: `rw [h]`

---

## Whitespace and Operators

Lean is whitespace-sensitive, and in general we opt for a style which avoids delimiting code.

### The `<|` and `|>` Operators

Sometimes parentheses can be avoided by judicious use of the `<|` operator (or its cousin `|>`).

> **Note:** While `$` is a synonym for `<|`, its use in Mathlib is disallowed in favor of `<|` for consistency as well as because of the symmetry with `|>`.

These operators have the effect of:
- **`<|`**: Parenthesizing everything to the right (note that `(` is curved the same direction as `<`)
- **`|>`**: Parenthesizing everything to the left (note that `)` curves the same way as `>`)

#### Common Usage of `|>`

Occurs with dot notation when the term preceding the `.` is a function applied to some arguments.

```lean
-- Instead of: ((foo a).bar b).baz
foo a |>.bar b |>.baz
```

#### Common Usage of `<|`

Occurs with dot notation when the term preceding the `.` is a function applied to multiple arguments whose last argument is a proof in tactic mode, especially one that spans multiple lines. Use `<| by ...` instead of `(by ...)`.

```lean
example {x y : ℝ} (hxy : x ≤ y) (h : ∀ ε > 0, y - ε ≤ x) : x = y :=
  le_antisymm hxy <| le_of_forall_pos_le_add <| by
    intro ε hε
    have := h ε hε
    linarith
```
