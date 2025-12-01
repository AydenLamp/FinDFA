# Mathlib Naming Conventions

This document contains comprehensive naming conventions for this project.

**Sources:**
* Lean Community website: <https://leanprover-community.github.io/index.html>
* Mathlib naming conventions: <https://leanprover-community.github.io/contribute/naming.html>

---

## Variable Naming Conventions

Use consistent variable names throughout your code:

- `x`, `y`, `z`, `u`, `v`, `w` ... for elements of a generic type (including elements of Semigroups and Monoids!)
- `e` ... for idempotent elements
- `s`, `t` ... for sets and lists
- `p`, `q`, `r` ... for predicates and relations (excluding Green's relations)
- `m`, `n`, `k` ... for natural numbers
- `i`, `j`, `k` ... for integers
- `a`, `b`, `c` ... for propositions
- `S`, `T` ... for semigroups
- `M` ... for monoids
- `G` ... for groups
- `α`, `β`, `γ` ... for generic types
- `u`, `v`, `w` ... for universes
- `h`, `h₁`, ... for assumptions

---

## Case Conventions

### `snake_case` (for Propositions)

Use `snake_case` for terms of type `Prop` (e.g., proofs, theorem names).

**Standard examples:** `add_comm`, `mul_assoc`, `lt_of_succ_le`, `le_of_lt`

### `UpperCamelCase` (for Types)

Use `UpperCamelCase` for:
1. File names
2. `Prop`s and `Type`s (e.g., inductive types, structures, and classes)

**Examples from this project:**
- `RPreorder`, `LPreorder`, `JPreorder`, `HPreorder` - Green's preorder relations
- `REquiv`, `LEquiv`, `JEquiv`, `HEquiv`, `DEquiv` - Green's equivalence relations
- `IsIdempotentElem` - predicate for idempotent elements

### `lowerCamelCase` (for Terms)

Use `lowerCamelCase` for all other terms of `Type`s (basically anything else).

**Examples from this project:**
- `pNatPow` - exponentiation function for semigroups
- `REquiv.set` - the R-class of an elemnent as a set

### Special Cases

**Functions** are named the same way as their return values. For example, a function of type `A → B → C` is named as though it is a term of type `C`.

**Acronyms** like `LE` are written upper or lowercase as a group, depending on what the first character would be. An exception is `Ne` and `Eq`.

**Types in theorem names:** When appearing in the names of theorems, `UpperCamelCase` types get `lowerCamelCase`d.

**Examples from this project:**
- `HEquiv.to_rEquiv` - converts `HEquiv` to `REquiv` (types become lowerca

**Namespaced definitions:** When referring to a namespaced definition in a lemma name not in the same namespace, the definition should have its namespace removed. If the definition name is unambiguous without its namespace, it can be used as is. Otherwise, the namespace is prepended back to it in `lowerCamelCase`. This ensures that `_`-separated strings in a lemma name correspond to a definition name or connective.

> **Note:** Within VS Code, hovering over any declaration such as `def Foo ...` will show the fully qualified name, like `MyNamespace.Foo` if `Foo` is declared while the namespace `MyNamespace` is open.

---

## Naming Dictionary

### Logic Operations

| Symbol | Shortcut | Name | Notes |
|--------|----------|------|-------|
| ∨ | `\or` | `or` | |
| ∧ | `\and` | `and` | |
| → | `\r` | `of` / `imp` | The conclusion is stated first and the hypotheses are often omitted |
| ↔ | `\iff` | `iff` | Sometimes omitted along with the right hand side of the iff |
| ¬ | `\n` | `not` | |
| ∃ | `\ex` | `exists` | |
| ∀ | `\fo` | `all` / `forall` | |
| = | | `eq` | Often omitted |
| ≠ | `\ne` | `ne` | |
| ∘ | `\o` | `comp` | |

### Algebra Operations

| Symbol | Shortcut | Name | Notes |
|--------|----------|------|-------|
| 0 | | `zero` | |
| + | | `add` | |
| - | | `neg` / `sub` | `neg` for unary function, `sub` for binary function |
| 1 | | `one` | |
| * | | `mul` | |
| ^ | | `pow` | |
| / | | `div` | |
| • | `\bu` | `smul` | |
| ⁻¹ | `\-1` | `inv` | |
| ⅟ | `\frac1` | `invOf` | |
| ∣ | `\|` | `dvd` | |
| ∑ | `\sum` | `sum` | |
| ∏ | `\prod` | `prod` | |

### Set Operations

| Symbol | Shortcut | Name | Notes |
|--------|----------|------|-------|
| ∈ | `\in` | `mem` | |
| ∉ | `\notin` | `notMem` | |
| ∪ | `\cup` | `union` | |
| ∩ | `\cap` | `inter` | |
| ⋃ | `\bigcup` | `iUnion` / `biUnion` | i for "indexed", bi for "bounded indexed" |
| ⋂ | `\bigcap` | `iInter` / `biInter` | i for "indexed", bi for "bounded indexed" |
| \ | `\\` | `sdiff` | |
| ᶜ | `\^c` | `compl` | |
| {x \| p x} | | `setOf` | |
| {x} | | `singleton` | |
| {x, y} | | `pair` | |

### Order Relations (Lattice)

| Symbol | Shortcut | Name |
|--------|----------|------|
| < | | `lt` / `gt` |
| ≤ | `\le` | `le` / `ge` |

#### Special Rules for `≤` and `<`

In Mathlib, we almost always use `≤` and `<` instead of `≥` and `>`, so we can use both `le`/`lt` and `ge`/`gt` for naming `≤` and `<`. There are a few reasons to use `ge`/`gt`:

1. **Different argument order:** We use `ge`/`gt` if the arguments to `≤` or `<` appear in different orders. We use `le`/`lt` for the first occurrence of `≤`/`<` in the theorem name, and then `ge`/`gt` indicates that the arguments are swapped.

   ```lean
   theorem lt_iff_le_not_ge [Preorder α] {a b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a
   theorem not_le_of_gt [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a
   theorem LT.lt.not_ge [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a
   ```

2. **Match argument order of another relation:** We use `ge`/`gt` to match the argument order of another relation, such as `=` or `≠`.

   ```lean
   theorem Eq.ge [Preorder α] {a b : α} (h : a = b) : b ≤ a
   theorem ne_of_gt [Preorder α] {a b : α} (h : b < a) : a ≠ b
   ```

3. **Describe swapped relation:** We use `ge`/`gt` to describe the `≤` or `<` relation with its arguments swapped.

   ```lean
   theorem ge_trans [Preorder α] {a b : α} : b ≤ a → c ≤ b → c ≤ a
   ```

4. **More variable second argument:** We use `ge`/`gt` if the second argument to `≤` or `<` is 'more variable'.

   ```lean
   theorem le_of_forall_gt [LinearOrder α] {a b : α} (H : ∀ (c : α), a < c → b < c) : b ≤ a
   ```

**Examples from this project:**

In Green's relations, we define lemmas that extract the directional components of equivalence relations:

```lean
-- REquiv.le extracts the "forward" direction: if x 𝓡 y, then x ≤𝓡 y
@[simp] lemma REquiv.le (h : x 𝓡 y) : x ≤𝓡 y

-- REquiv.ge extracts the "backward" direction: if x 𝓡 y, then y ≤𝓡 x  
@[simp] lemma REquiv.ge (h : x 𝓡 y) : y ≤𝓡 x
```

---

## Theorem Naming

### Descriptive Naming

Definitions and theorem names should describe their conclusion. Use the naming dictionaries above for standard operations in that conclusion.

**Infix operations:** When an operation is written as infix, the theorem names follow suit. For example, we write `neg_mul_neg` rather than `mul_neg_neg` to describe the pattern `-a * -b`.

### Referring to Hypotheses with `of`

Sometimes, to disambiguate the name of a theorem or better convey the intended reference, it is necessary to describe some of the hypotheses. The word `of` is used to separate these hypotheses.

**Examples from this project:**
- `REquiv.of_rPreorder_and_jEquiv` - creates 𝓡-equivalence from 𝓡-preorder and 𝓙-equivalence

**Standard examples:**
- `lt_of_succ_le`
- `lt_of_not_ge`
- `lt_of_le_of_ne`
- `add_lt_add_of_lt_of_le`

**Important:** The hypotheses are listed in the order they appear, not reverse order. For example, the theorem `A → B → C` would be named `C_of_A_of_B`.

### Axiomatic Naming

Some theorems are better described using axiomatic names. Common "axiomatic" properties of an operation like introduction and elimination are put in a namespace that begins with the name of the operation. In particular, this includes `intro` and `elim` operations for logical connectives, and properties of relations.

**Examples from this project:**
- `refl`, `symm`, `trans` in `REquiv`, `LEquiv`, `JEquiv`, `HEquiv` - standard equivalence properties

**Standard examples:**
- `And.comm`, `And.intro`, `And.elim`
- `Or.comm`, `Or.intro_left`, `Or.intro_right`
- `Or.resolve_left`, `Or.resolve_right`
- `Eq.trans`, `HEq.trans`
- `Iff.refl`

**Common axiomatic descriptions:**
- `def` (for unfolding a definition)
- `assoc`
- `refl`
- `symm`
- `trans`
- `irrefl`
- `antisymm`
- `asymm`
- `congr`
- `comm`
- `left_comm`
- `right_comm`
- `mul_left_cancel`
- `mul_right_cancel`
- `inj` (injective)

### Extensionality

- A lemma of the form `(∀ x, f x = g x) → f = g` should be named `.ext`, and labelled with the `@[ext]` attribute.
- A lemma of the form `f = g ↔ ∀ x, f x = g x` should be named `.ext_iff`.

### Injectivity

Where possible, injectivity lemmas should be written in terms of an `Function.Injective f` conclusion which uses the full word injective, typically as `f_injective`.

In addition to these, a variant should usually be provided as a bidirectional implication, e.g., as `f x = f y ↔ x = y`, which can be obtained from `Function.Injective.eq_iff`. Such lemmas should be named `f_inj` (although if they are in an appropriate namespace `.inj` is good too). Bidirectional injectivity lemmas are often good candidates for `@[simp]`.

An injectivity lemma that uses "left" or "right" should refer to the argument that "changes". For example, a lemma with the statement `a - b = a - c ↔ b = c` could be called `sub_right_inj`.

### Predicates as Prefixes

Most predicates should be added as prefixes. For example, `IsClosed (Icc a b)` should be called `isClosed_Icc`, not `Icc_isClosed`.

**Exception:** Some widely used predicates don't follow this rule. Those are the predicates that are analogous to an atom already suffixed by the naming convention. Here is a non-exhaustive list:

- We use `_inj` for `f a = f b ↔ a = b`, so we also use `_injective` for `Injective f`, `_surjective` for `Surjective f`, `_bijective` for `Bijective f`...
- We use `_mono` for `a ≤ b → f a ≤ f b` and `_anti` for `a ≤ b → f b ≤ f a`, so we also use `_monotone` for `Monotone f`, `_antitone` for `Antitone f`, `_strictMono` for `StrictMono f`, `_strictAnti` for `StrictAnti f`, etc...
