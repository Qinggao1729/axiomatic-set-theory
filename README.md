# Axiomatic Set Theory in Lean 4

**Project scope:** standalone research formalization following Enderton.  
**Acknowledgments:** [ACKNOWLEDGMENTS.md](ACKNOWLEDGMENTS.md).

This repository formalizes Herbert Enderton's *Elements of Set Theory* in Lean 4, using a primitive `Set` type and primitive membership relation `∈`, then building definitions and theorems chapter-by-chapter in textbook order.

## Why This Repo Exists

This project is both:

- a machine-checked development of textbook set theory, and
- a pedagogical formalization that makes hidden assumptions explicit (carriers for comprehension, nonempty side-conditions for intersections, function-value well-definedness, AC usage boundaries, etc.).

Mathlib imports are intentionally minimal for foundational material so the core thread is rebuilt explicitly rather than inherited from higher-level abstractions.

## Current Human-Checked Scope

From the project writeup in `Writeups/CS263 Project Report.md`:

- Chapter 2
- Chapter 3 Sections 1–4
- Chapter 4 Section 1

The repository also implements Chapter 3 Sections 5–7 (infinite Cartesian products, equivalence relations, ordering relations), which are not yet at the same audit maturity. Later chapters (Chapter 4 Section 2 onward, and Chapter 5) are planned but not yet in the repository.

## Quick Start

### Prerequisites

- Lean 4 via [elan](https://github.com/leanprover/elan)
- Lake (bundled with Lean)

### Build

```bash
cd axiomatic-set-theory
lake exe cache get   # optional, speeds first build
lake build
```

Default target is the `Set` library.

## Repository Layout (Start Here)

- `Set.lean` — root import for chapter aggregators.
- `Set/Axioms.lean` — primitive layer: `Set`, `∈`, `⊆`, core axioms (Ch2 + primitive infinity).
- `Set/Ch2/` — axioms unpacked into concrete constructions, arbitrary unions/intersections, algebra of sets.
- `Set/Ch3/` — ordered pairs, relations, n-ary relations, functions, infinite products/choice, equivalence, orderings.
- `Set/Ch4/` — inductive sets, the Infinity axiom, `ω`, and induction on `ω` (S1; later sections planned).
- `Set/Choice.lean` — central home for AC forms in `Set.Choice` namespace.
- `Set/SimpAttrs.lean` — custom simp attribute `set_spec_simps`.
- `docs/textbook-transcriptions/` — section-by-section textbook extraction notes.
- `TODO.md` — master checklist mapping set-theoretic statements to Lean declarations.

## Core Design Patterns

### 1) Axioms -> `Classical.choose` -> `*.Spec`

Most canonical objects follow:

1. existential axiom (`∃ B, ...`) in primitive layer,
2. `noncomputable def` via `Classical.choose`,
3. membership specification lemma `Name.Spec`.

This keeps set construction explicit and proof automation local.

### 2) `set_spec_simps` for specification unfolding

`*.Spec` lemmas are accumulated under a custom simp attribute, so proofs can use:

```lean
simp only [set_spec_simps]
simp_all only [set_spec_simps]
```

This avoids long manual rewrite chains.

### 3) Ordered-pair notation choice

Project preference in section proofs is `⟪x, y⟫` (distinct from Lean constructor `⟨...⟩`) to reduce visual ambiguity in proofs.

### 4) Infinity axiom structure

`Set/Axioms.lean` contains a primitive infinity axiom form (with explicit empty/successor-like witnesses).  
`Set/Ch4/S1_InductiveSets.lean` `#check`s it and derives Enderton's shorthand form `∃ A, Inductive A`.

### 5) AC visibility policy

AC declarations are centralized in `Set/Choice.lean` under `Set.Choice`.  
Consumers either `open Choice` or qualify names, making AC dependence explicit.

In `Set/Ch3/S4_Functions.lean`, only genuinely AC-dependent declarations (notably 3J(b)) live in `namespace Choice`; AC-free results remain in plain `Set`.

## Workflow for New Sections (Mandatory)

Use `workflow.md` as the source of truth. In short:

1. Read textbook section first.
2. Draft/update transcription in `docs/textbook-transcriptions/`.
3. Update `TODO.md` with checkbox + set-theory line + Lean declaration line.
4. Implement in matching `Set/Ch#/S*_*.lean` file.
5. Build and sync TODO status with actual code.

Synchronization rule: TODO and corresponding Lean section must match.

## Proof Style Summary

Before proof edits, read `proof_style.md`.

Core expectations:

- visible proof skeleton (`intro`, `constructor`, `extensionality`),
- reuse existing theorems before manual decomposition,
- use `simp`/`simp_all` (especially with `set_spec_simps`) for routine logic,
- avoid opaque heavy automation in final foundational proofs (`aesop` as search aid only),
- keep AC boundaries explicit (`namespace Choice` only when AC is actually used).

## Progress Tracking

Use `TODO.md` for:

- per-section statement mapping (set-theory text <-> Lean names),
- checked vs pending items,
- chapter-level status snapshot.

## Known Limitations

- Later chapters (Chapter 4 Section 2 onward, and Chapter 5) are planned but not yet present in the repository.
- Some prose docs can lag code after refactors; when in doubt, trust `.lean` files and `lake build`.