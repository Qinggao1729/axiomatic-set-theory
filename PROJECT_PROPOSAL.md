# Project proposal: formalizing Enderton’s *Elements of Set Theory*

This document answers four planning questions: **(1)** software and infrastructure, **(2)** the project idea, **(3)** what remains to learn or investigate, and **(4)** success criteria.

## Goal

Machine-check Enderton’s *Elements of Set Theory* in **Lean 4**: primitive `Set` and membership, axioms as in the book, then relations, functions, \( \omega \), recursion, arithmetic, and Chapters 2–5 toward the reals. Same broad motivation as other textbook formalizations (e.g. Tao’s *Analysis*): gaps become visible, and the result is a reusable, auditable line of definitions and proofs.

## Project idea (scope)

- **Core:** ZFC-style axioms aligned with early Enderton; develop through **relations, functions, choice-related material, `ω`, Peano, recursion, arithmetic, reals** as in the book.
- **Artifact:** Library under `Set/Ch*/S*.lean`, with `*.Spec` lemmas, `Enderton_Textbook_Todos.md`, and `docs/textbook-transcriptions/` kept in sync with Enderton’s *Elements of Set Theory* (local PDF optional; not committed).
- **Non-goals:** Replacing all of Mathlib or competing with Mathlib’s general mathematics; only **Enderton’s thread**.

## Software and infrastructure

| Piece | Use in this project |
|--------|----------------------|
| **Lean 4** | Proof assistant and language (version pinned in `lean-toolchain`). |
| **Lake** | Build system and dependency management (`lakefile.toml`). |
| **Mathlib** | Declared as a **dependency** so the project stays in the standard Lean 4 ecosystem. **Imports from Mathlib are minimized** in source files; the formalized mathematics is **not** built on Mathlib’s general `Set`/`Nat` story—see `Set/Axioms.lean` and `Set/Ch*/…`. |
| **SMT solvers** | **Not used.** Proofs are interactive tactic scripts in Lean, not outsourced to Z3/CVC4/etc. |
| **Other libraries** | **Aesop** (proof search) is used where already wired in the repo; no other major libraries are assumed beyond what Lake pulls transitively. **Batteries** / core libraries ship with the usual Lean setup. |

## Imports and tactics (project policy)

1. **Minimize Mathlib imports.** Prefer core/batteries tactics (`intro`, `rw`, `simp`, `exact`, …) and what the repo already uses; do not grow dependencies without a reason.

2. **\( \mathbb{Z} \), \( \mathbb{Q} \), \( \mathbb{R} \) (as formalized here): prove by hand first**—your own lemmas for associativity, commutativity, inverses, etc., with `rw` / `simp` / `calc`. That matches the book and keeps the story on **`Set`**-level constructions.

3. **Use `ring`, `linarith`, `omega`, `norm_num`, and similar only as a last resort** when you are genuinely stuck. They expect **typeclass-backed** arithmetic (e.g. `CommRing` for `ring`); they do not apply to raw `Set`-valued equalities unless you **explicitly** add a separate type/instance layer for automation—and that is **not** the default plan.

4. **Search tactics** (`exact?`, `simp?`, `aesop?`, …): allowed for discovery; **replace** the finished proof with a readable script (`proof_style.md`).

## Open questions and learning (what we still need to figure out)

- **Reals (Chapter 5):** Full Dedekind-cut development, order, and algebra is large; which theorems to prioritize and what can stay `sorry` temporarily is still open.
- **Axiom phrasing vs the book:** Relating the primitive `infinity` (and similar) to Enderton’s prose may need extra bridge lemmas and clear documentation.
- **Choice / AC:** Tracking which results use classical choice or global classical principles, and stating that consistently (comments or lemma names).
- **Automation vs readability:** How much `simp` / `aesop` is acceptable in “final” proofs without obscuring the mathematical argument (`proof_style.md` is the contract; practice will refine it).
- **Maintenance:** Keeping TODO lists, transcriptions, and Lean files aligned under refactors (e.g. `Comprehension`, implicit `*.Spec` arguments).

## Success criteria

- **Coverage:** Through Chapter 5, main **definitions and theorems** from Enderton appear in the chapter/section file layout; the hardest **real-number** block may be incomplete or use `sorry`, explicitly tracked in `Enderton_Textbook_Todos.md`.
- **Build:** `lake build` succeeds for the main library target.
- **Quality:** Proofs remain **readable**—reuse of `*.Spec` and `set_spec_simps`, avoidance of unnecessary opaque automation, hand proofs preferred for \( \mathbb{Z} \)/\( \mathbb{Q} \)/\( \mathbb{R} \) unless stuck (see policy above).
- **Traceability:** Book statements map to Lean names via the TODO file and `docs/textbook-transcriptions/`.
- **Onboarding:** A new contributor can use `PROJECT_GUIDE.md`, a local copy of the book (or transcriptions), and `workflow.md` to extend one section without reverse-engineering the whole repo.
