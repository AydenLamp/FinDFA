# Lean/Mathlib Documentation Standards

This document contains documentation standards for Lean 4 code and Mathlib contributions.

**Sources:**
* Lean Community website: <https://leanprover-community.github.io/index.html>
* Library Style Guidelines: <https://leanprover-community.github.io/contribute/style.html>

---

## Comments

Use different comment styles for different purposes:

- **Module docs** (`/-! ... -/`): Section headers and separators (incorporated into auto-generated docs)
- **Technical comments** (`/- ... -/`): TODOs, implementation notes, comments in proofs
- **Short comments** (`--`): Short or in-line comments

---

## Declaration Docstrings

Documentation strings for declarations are delimited with `/-- ... -/`. 

### Rules

- Place the docstring directly above the declaration
- When a documentation string spans multiple lines, do not indent subsequent lines
- Every definition and major theorem is required to have a doc string
- Doc strings on lemmas are encouraged, particularly if the lemma has any mathematical content or might be useful in another file
- Use newlines or single spaces between the markers (`/--`, `-/`) and the text
- If a doc string is a complete sentence, it should end in a period
- Named theorems should be bold faced (i.e., with two asterisks before and after)

### Purpose

Doc strings should convey the mathematical meaning of the definition. They are allowed to lie slightly about the actual implementation.

### Examples

**Example:**

```lean
/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)
```

**Example (slightly abstract but mathematically accurate):**

```lean
/-- `padicValRat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to `0`. -/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den
```

---

## Module Docstrings

Each file must start with a module docstring.

### Format

- The open and close delimiters `/-!` and `-/` should appear on their own lines
- The mandatory title of the file is a first level header (`#`)
- It is followed by a summary of the content of the file

### Sections (in this order)

1. **Main definitions** (optional, can be covered in the summary)
2. **Main statements** (optional, can be covered in the summary)
3. **Notations** (omitted only if no notation is introduced in this file)
4. **Implementation notes** (description of important design decisions or interface features, including use of type classes and `simp` canonical form for new definitions)
5. **References** (references to textbooks or papers, or Wikipedia pages)

### Example

```lean
/-!
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* <https://en.wikipedia.org/wiki/P-adic_number>
-/
```

---

## File Structure

It is common to structure a file in sections, where each section contains related declarations. By describing the sections with module documentation `/-! ... -/` at the beginning, these sections can be seen in the documentation.

### Important Notes

- While these sectioning comments will often correspond to `section` or `namespace` commands, this is not required
- You can use sectioning comments inside of a section or namespace
- You can have multiple sections or namespaces following one sectioning comment
- Sectioning comments are for display and readability only. They have no semantic meaning
- Third-level headers `###` should be used for titles inside sectioning comments
- If the comment is more than one line long, the delimiters `/-!` and `-/` should appear on their own lines

### Example

```lean
/-!
### Basic properties

This section contains basic lemmas about the norm.
-/

-- Declarations here...

/-!
### Algebraic properties
-/

-- More declarations...
```

---

## Examples of Good Documentation

The following files are maintained as examples of good documentation style:
- `Mathlib.NumberTheory.Padics.PadicNorm`
- `Mathlib.Topology.Basic`
- `Analysis.Calculus.ContDiff.Basic`
