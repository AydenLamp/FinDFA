# Lean Blueprint Guide

This guide explains how to use and edit the Lean Blueprint in this project.

**leanblueprint repository:** https://github.com/PatrickMassot/leanblueprint

---

## Table of Contents

1. [Overview](#overview)
2. [Project Structure](#project-structure)
3. [Getting Started](#getting-started)
4. [Editing the Blueprint](#editing-the-blueprint)
5. [Blueprint Entry Structure](#blueprint-entry-structure)
6. [Essential LaTeX Macros](#essential-latex-macros)
7. [Local Development Workflow](#local-development-workflow)

---

## Overview

This project uses **leanblueprint** for interactive documentation. When you push changes to this repository, **GitHub Actions** automatically compiles the LaTeX files in the `LaTeX/` directory and generates an interactive web version with a dependency graph. This is then automatically deployed to GitHub Pages and can be viewed at https://lean-summer-research.github.io/finalized/.

---

## Project Structure

Our blueprint currently has **one LaTeX file per Lean file**:

Each `.tex` file should document the mathematical content of its corresponding `.lean` file.

---

## Getting Started

### Dependencies

**If you're using this project's dev container or GitHub Codespace:**  
All dependencies are pre-installed.

**If you're working locally:**  
You need to install the leanblueprint tool and its dependencies. See the [leanblueprint repository](https://github.com/PatrickMassot/leanblueprint) for installation instructions.

---

## Adding a New LaTeX File

After creating a new LaTeX file in `LaTeX/`, include it by editing `LaTeX/Chapters.tex`:
   ```latex
\input{../../LaTeX/NewFile.tex}
   ```

## Blueprint Entry Structure

### Basic Theorem Structure

```latex
\begin{theorem}[Theorem Name]
  \label{thm:unique_label}
  \lean{lean_declaration_name}
  \leanok  % Include if fully formalized
  \uses{dep1, dep2}  % Dependencies
  
  Mathematical statement goes here using standard LaTeX math notation.
\end{theorem}

\begin{proof}
  \leanok  % Include if proof is complete in Lean
  \uses{proof_dep1, proof_dep2}  % Proof dependencies
  
  Proof explanation goes here. 
\end{proof}
```

Note that a theorem's proof must not list the theorem itself as its own dependency.

### Definition Structure

```latex
\begin{definition}[Definition Name]
  \label{def:unique_label}
  \lean{lean_definition_name}
  \leanok
  
  A mathematical object $X$ is called a \emph{special thing} if it satisfies
  the following properties...
\end{definition}
```

### Lemma and Proposition Structure

```latex
\begin{lemma}[Lemma Name]
  \label{lem:unique_label}
  \lean{lean_lemma_name}
  \uses{thm:main_theorem}
  
  Statement of the lemma...
\end{lemma}
```

---

## Essential LaTeX Macros

These macros connect your LaTeX documentation to your Lean code:

### `\lean{declaration_name}`
Lists the Lean declaration names corresponding to the surrounding definition or statement.

```latex
\begin{theorem}[Commutativity of Addition]
  \label{thm:add_comm}
  \lean{add_comm}
  For all natural numbers $a$ and $b$, we have $a + b = b + a$.
\end{theorem}
```

### `\leanok`
Claims that the surrounding environment is fully formalized in Lean.

```latex
\begin{theorem}[Fermat's Little Theorem]
  \lean{fermat_little_theorem}
  \leanok  % This theorem is completely proved in Lean
  If $p$ is prime and $a$ is not divisible by $p$, then $a^{p-1} \equiv 1 \pmod{p}$.
\end{theorem}
```

### `\uses{label1, label2}`
Lists LaTeX labels that are used in the surrounding environment (for dependency tracking).

```latex
\begin{theorem}[Main Result]
  \label{thm:main}
  \lean{main_theorem}
  \uses{def:group, lem:helper}
  This theorem depends on the group definition and helper lemma.
\end{theorem}
```

### Additional Macros

- `\notready` - Marks that the environment is not ready to be formalized
- `\mathlibok` - Marks nodes that were already merged into Mathlib
- `\discussion{issue_number}` - References a GitHub issue for discussion
- `\proves{label}` - Used in proofs to specify which theorem is being proved

---

## Local Development Workflow

### 1. Edit LaTeX Files
Make your changes to files in the `LaTeX/` directory.

### 2. Compile Locally
Open a terminal in VS Code (Ctrl + `) and run:

```bash
leanblueprint all
```

This command:
- Builds the PDF version
- Builds the web version
- Checks that all Lean declarations exist

### 3. Serve Locally
After compilation, start a local web server:

```bash
leanblueprint serve
```

Click the provided link (usually `http://0.0.0.0:8000/`) to view your blueprint locally.

### 4. Commit and Push
Once you're satisfied with your changes:

```bash
git add LaTeX/
git commit -m "Update blueprint documentation"
git push
```

The GitHub Pages will be automatically updated after the GitHub Action completes. You can monitor the build process in the "Actions" tab of the GitHub repository.

