# Formalization Workflow (Per Section)

This document defines the standard workflow for each textbook section in this repo.

## 0) Scope and Goals

- Goal: follow textbook logic order strictly, then formalize in Lean.
- Coverage target per section: axioms, definitions, theorems, examples, and key proof ideas.
- Synchronization rule: TODO section and corresponding `.lean` section must stay aligned at all times.

## 1) Read Textbook First

For each new section:

0. Use the textbook as the primary source:
   - A **local** PDF (standard filename is gitignored) and/or the section transcription under `docs/textbook-transcriptions/`.
   - Extract statements/proof flow before writing Lean or TODO items.
1. Read the textbook section fully before coding.
2. Identify:
   - Definitions
   - Axioms
   - Theorems/Lemmas/Corollaries
   - Examples/exercises used in narrative
3. Keep theorem order consistent with the textbook unless there is a hard Lean dependency issue.
4. For Chapter 4 Section 3 specifically:
   - Keep `Set/Ch4/S3_RecursionOnOmega.lean` focused on the recursion theorem chain and 4H.
   - Place arithmetic-specific specializations (e.g. successor graph wrappers used by addition/multiplication) in `Set/Ch4/S4_Arithmetic.lean`.

## 2) Create a Section Extraction Draft

Before formalizing:

1. Create/update a section transcription file under:
   - `docs/textbook-transcriptions/`
   - Example: `docs/textbook-transcriptions/ch2/ch2s3.md`
   - Example: `docs/textbook-transcriptions/ch3/ch3s6.md`
2. Record:
   - Formal statements (set-theoretic)
   - Human-written proof sketch from textbook
   - Any diagrams or narrative proof steps rewritten as text
3. Prefer preserving textbook proof flow, especially for multi-step equivalence proofs.

## 3) Update TODO First (Planning Contract)

Add/update the corresponding section in `TODO.md` before proving.

Required format per item:

- Checkbox item:
  - `- [ ]` pending, `- [x]` done
- Two child lines:
  - `- **Set theory:** ...`
  - `- **Lean:** ...`

Rules:

- Use concrete declaration names/signatures from the real `.lean` file.
- Do not include decorators like `@[simp]` in TODO.
- Every section must include primary Lean file reference(s).

## 4) Formalize in Lean

Implementation order:

1. Add core definitions and notation first.
2. Add `*.Spec` lemmas.
3. Add uniqueness theorems when applicable.
4. Add derived theorems/examples following textbook order.

When writing proofs, always consult:

- `proof_style.md`
- `.cursor/rules/Lean-proof-style-protocol.mdc`

## 5) Proof Style Requirements (Operational)

- Keep semantic steps explicit; use `simp` for routine logical plumbing.
- Prefer theorem reuse before manual decomposition.
- Use `exact` directly when goal matches hypothesis/projection.
- Use `rw` when rewrite is simple and transparent.
- For repeated spec rewrites, prefer:
  - `simp only [set_spec_simps]`
  - `simp_all only [set_spec_simps]`
- In branch cases, prefer short visible steps (`apply` -> `rw` -> `exact`) over one complex term.
- If stuck:
  1. try `aesop?` as search only
  2. rewrite final proof into explicit + simp style

## 6) Tactics / Metaprogramming Support

- Allowed and encouraged when they improve maintainability and readability.
- For spec-heavy work, maintain/use custom simp set infrastructure (`Set/SimpAttrs.lean`).
- Avoid introducing abstraction wrappers that add proof noise unless there is a clear meta-level benefit.

## 7) Verification Loop

After substantial edits:

1. Typecheck target file/module.
2. Run build for impacted module(s).
3. Fix new errors immediately.
4. Update TODO checkboxes to match actual proof status.
5. Keep temporary transcription file updated when it aids proof maintenance.

## 8) Definition of Done (Per Section)

A section is done only when all conditions hold:

- Textbook items are transcribed and mapped.
- Lean file contains finalized definitions/theorems in intended order.
- Proofs follow `proof_style.md`.
- TODO section is fully synchronized with Lean content.
- Build/typecheck passes for impacted modules.

