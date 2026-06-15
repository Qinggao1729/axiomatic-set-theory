# Architecture Changes for Ch.2–Ch.4 Formalization

_File renamed from `ARCHITECTURE_CH2_CH3_FORMALIZATION.md`; it describes the Chapter 2–4 section-module layout._

This document explains the structural changes made while formalizing the Chapter 2/3/4 items from Enderton.

## 1) New/Extended Modules

The implementation is now physically split by textbook sections:

- Chapter 2 implementation lives in:
  - `Set/Ch2/S1_Axioms.lean` (`no_universal_set`)
  - `Set/Ch2/S2_ArbitraryUnionsIntersections.lean` (`intersection`, `BigIntersection`, related lemmas)
  - `Set/Ch2/S3_AlgebraOfSets.lean` (binary algebra laws, monotonicity, generalized family laws)

- Chapter 3 implementation lives in:
  - `Set/Ch3/S1_OrderedPairs.lean` (ordered pairs, 3A/3B/3C, `Product`)
  - `Set/Ch3/S2_Relations.lean` (3D and relation/domain/range/field API)
  - `Set/Ch3/S3_NAryRelations.lean` (n-ary relation encodings)
  - `Set/Ch3/S4_Functions.lean` (functions core, 3E/3F/3G/3H/3I/3K/3L, plus 3J(a) AC-free in the plain `Set` namespace and 3J(b) inside a reopened `Choice` namespace — only declarations that genuinely use AC live in `Choice`; two `#print axioms` lines at the bottom of the file enforce the split)
  - `Set/Ch3/S5_InfiniteCartesianProducts.lean` (infinite products and second-form AC)
  - `Set/Ch3/S6_Equivalence.lean` (3M/3N/3P + quotient/compatibility + 3Q statements)
  - `Set/Ch3/S7_OrderingRelations.lean` (linear order definitions and 3R consequences)

- Chapter 4 implementation lives in:
  - `Set/Ch4/S1_InductiveSets.lean` (4A/4B/4C and core natural-number construction;
    derives Enderton's shorthand Infinity statement
    `infinity_inductive : ∃ A, Inductive A` from the primitive axiom, and
    defines the chosen witness `Infinity := Classical.choose infinity_inductive`)
  - Note: the primitive Infinity axiom now lives in `Set/Axioms.lean` in
    witness-expanded form; `Set/Ch4/S1_InductiveSets.lean` derives the
    Enderton literal shorthand `∃ A, Inductive A` as a theorem.
  - Chapter 4 Sections 2 onward (Peano postulates, recursion on `ω`, arithmetic,
    ordering on `ω`) are planned but not yet in the repository.

Use the chapter aggregators (`Set/Ch2.lean`, `Set/Ch3.lean`, …) and section
files directly. Older one-line re-export shims under `Set/*.lean` have been
removed to avoid a parallel “old layout” import graph; `Set/Choice.lean` remains
the home for choice-axiom declarations referenced from Chapter 3.

## 1.5) Chapter/Section File Layout

Refactored to chapter/section aggregator files matching textbook flow:

- `Set/Ch2/S1_Axioms.lean`
- `Set/Ch2/S2_ArbitraryUnionsIntersections.lean`
- `Set/Ch2/S3_AlgebraOfSets.lean`
- `Set/Ch2.lean` (aggregator)

- `Set/Ch3/S1_OrderedPairs.lean`
- `Set/Ch3/S2_Relations.lean`
- `Set/Ch3/S3_NAryRelations.lean`
- `Set/Ch3/S4_Functions.lean`
- `Set/Ch3/S5_InfiniteCartesianProducts.lean`
- `Set/Ch3/S6_Equivalence.lean`
- `Set/Ch3/S7_OrderingRelations.lean`
- `Set/Ch3.lean` (aggregator)

- `Set/Ch4/S1_InductiveSets.lean`
- `Set/Ch4.lean` (aggregator)

And top-level:

- `Set.lean` imports `Set.Ch2`, `Set.Ch3`, and `Set.Ch4`.

## 2) Why AC Is Structured This Way

To keep future “six equivalent forms of AC” development clean:

- AC declarations are kept out of `Set/Axioms.lean` (which only contains core set axioms).
- Forms are introduced in-place in their chapter sections:
  - Form I in `Set/Ch3/S4_Functions.lean` as `Set.ChoiceFirstForm`,
    with `Set.Choice.choice_first_form` declared in a short `Choice` block.
  - Form II in `Set/Ch3/S5_InfiniteCartesianProducts.lean` as
    `Set.ChoiceSecondForm`, with only the axiom and AC-dependent
    consequences in `Set.Choice`.
- `Set/Choice.lean` remains the shared home for non-local forms (III/IV/VI)
  and AC infrastructure. It keeps function predicates inline as
  `IsRelation H ∧ ∀ x ∈ dom H, ∃! y, ⟪x, y⟫ ∈ H`, avoiding dependency on
  chapter-specific `IsFunction` definitions.
- AC consumers:
  - `Set/Ch3/S4_Functions.lean` introduces `ChoiceFirstForm` in plain
    `Set`, enters/exits `Choice` immediately for the axiom declaration,
    then reopens `Choice` **only** for Theorem 3J(b) — the one proof that
    actually invokes `choice_first_form`. Theorem 3J(a) and its helpers
    (`LeftInverseRelation`, `one_to_one_preimage_unique`) stay in plain
    `Set` because they are AC-free.
  - `Set/Ch3/S5_InfiniteCartesianProducts.lean` `open`s `Choice` once at
    the top and `#check`s the second-form declaration for the
    infinite-product nonempty theorem.
- Forms are named as separate logical objects (`ChoiceFirstForm`, `ChoiceSecondForm`) so additional forms can be appended naturally:
  - `ChoiceThirdForm`, `ChoiceFourthForm`, ...
- Equivalence proofs can then be added as ordinary theorems between these forms, without changing existing theorem files.

This avoids circular dependencies and allows incremental strengthening without refactoring prior proofs.

## 3) Build Integration

- `Set.lean` imports chapter aggregators:
  - `Set.Ch2`
  - `Set.Ch3`
  - `Set.Ch4`

So `lake build` (default target `Set`) checks the new formalization modules automatically.

## 4) Axiom Index

- Added `Set/AxiomIndex.md` to record:
  - first textbook appearance (chapter/section/page),
  - declaration location in code.

