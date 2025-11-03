# Mathlib Best Practices

This document contains high-level coding practices and guidelines for Lean 4 code and Mathlib contributions.

**Sources:**
* Lean Community website: <https://leanprover-community.github.io/index.html>
* Library Style Guidelines: <https://leanprover-community.github.io/contribute/style.html>

---

## Normal Forms

Some statements are equivalent. For instance, there are several equivalent ways to require that a subset `s` of a type is nonempty. For another example, given `a : α`, the corresponding element of `Option α` can be equivalently written as `Some a` or `(a : Option α)`.

**General principle:** We try to settle on one standard form, called the **normal form**, and use it both in statements and conclusions of theorems.

**Examples of normal forms:**
- `s.Nonempty` (which gives access to dot notation)
- `(a : Option α)` instead of `Some a`

Often, `simp` lemmas will be registered to convert the other equivalent forms to the normal form.

---

## Simp Lemmas

### Squeezing `simp` Calls

Unless performance is particularly poor or the proof breaks otherwise, **terminal `simp` calls should not be squeezed** (replaced by the output of `simp?`).

**Definition:** A `simp` call is terminal if it closes the current goal or is only followed by flexible tactics such as `ring`, `field_simp`, or `aesop`.

**Reasons for not squeezing terminal simp calls:**

1. **Readability:** A squeezed `simp` call might be several lines longer than the corresponding unsqueezed one, and therefore drown the useful information of what key lemmas were added to the unsqueezed `simp` call to close the goal in a sea of basic `simp` lemmas.

2. **Maintenance:** A squeezed `simp` call refers to many lemmas by name, meaning that it will break when one such lemma gets renamed. Lemma renamings happen often enough for this to matter on a maintenance level.

---

## Iff Theorems

Iff theorems should be notated such that the **more normalized version of the statement is on the right side** of the iff.

**Benefits:**
- This allows you to use them with `rw` and `simp` without prepending `←`
- This is also the way that `simp` will try to automatically apply the tactic if you tag it `@[simp]`

**Example:**

```lean
-- Preferred (normalized form on the right)
theorem mem_setOf {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a

-- Not preferred
theorem mem_setOf {a : α} {p : α → Prop} : p a ↔ a ∈ {x | p x}
```
