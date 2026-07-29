# Formalization Workflow (Per Section)

This is the required workflow for every new section.

## 1) Literal Transcription from Images

1. Use section page images under `textbook-pages-by-sections/` as the source of truth.
2. Create/update `docs/textbook-transcriptions/chX/chXsY.md`.
3. Transcribe literally (word-by-word), including page markers.
4. Do not transcribe from PDF text extraction.

Both directories are gitignored: the textbook is under copyright (Academic Press, 1977), so page images and literal transcriptions are working material that stays on your machine. Only the short attributed quotations in Lean doc-comments are published.

## 2) Extract What Must Be Formalized

From the transcription, list all formalizable textbook items:

- Definitions
- Alternative definitions / equivalent formulations
- Axioms
- Theorems / lemmas / corollaries

Do not formalize exercises.  
Examples and narrative are included only when they are needed for proof structure or later reuse (use judgment).

## 3) Formalize Completely in Lean

1. Ensure every required item from Step 2 has a corresponding Lean declaration.
2. Keep declaration order close to textbook flow unless Lean dependencies force a change.
3. For each textbook-facing declaration, follow `proof_style.md`:
   - naming conventions (including numbered declaration style when applicable)
   - doc-comment citation format
   - proof readability/style conventions
4. Required citation comment format:
   - `/-- [Enderton ChN §M, p.PP] "literal textbook wording." -/`
   - use `pp.PP-QQ` for page ranges.

## 4) Completeness Audit Against Transcription

Before considering a section translated:

1. Compare transcription item-by-item against Lean declarations.
2. Confirm all required definitions/alternative definitions/axioms/theorems/lemmas/corollaries are present.
3. Add a `Mapping to Lean` section in the transcription file.

## 5) Update TODO (Unchecked)

Update the section in `TODO.md` so it matches the current Lean declarations and mapping.

- Add missing items and Lean names/signatures as needed.
- Keep new/updated items unchecked (`[ ]`) until human verification.

## 6) Verify

1. Typecheck/build impacted modules.
2. Fix any new errors.
3. Re-check that TODO, transcription mapping, and Lean declarations are synchronized.

