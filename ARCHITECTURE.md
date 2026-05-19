# Architecture Changes for Ch.2/Ch.5 Formalization

_File renamed from `ARCHITECTURE_CH2_CH3_FORMALIZATION.md`; it describes the Chapter 2–5 section-module layout._

This document explains the structural changes made while formalizing the remaining Chapter 2/3/4/5 items from Enderton.

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
    also the home of the **Infinity Axiom** in Enderton's literal form
    `∃ A, Inductive A`, plus the chosen witness `Infinity := Classical.choose infinity`)
  - `Set/Ch4/S2_PeanosPostulates.lean` (Peano-system layer and 4D/4E/4F/4G line)
  - `Set/Ch4/S3_RecursionOnOmega.lean` (recursion theorem on `ω` and 4H)
  - `Set/Ch4/S4_Arithmetic.lean` (4I/4J/4K arithmetic layer)
  - `Set/Ch4/S5_OrderingOnOmega.lean` (4L/4M/4N/4P, well-ordering, and strong-induction layer)
  - Note: the Infinity axiom is the **only** Enderton axiom that does not live in
    `Set/Axioms.lean`, because its statement uses `∅`, `Successor`, and
    `Inductive`, which are themselves defined in `Set/Ch4/S1_InductiveSets.lean`.
    `Set/Axioms.lean` carries a comment pointing to the actual declaration site,
    and `Set/AxiomIndex.md` lists the location alongside the Ch2 axioms.

- Chapter 5 implementation now lives in:
  - `Set/Ch5/S1_Integers.lean` (integer construction scaffold, 5ZA–5ZL line)
  - `Set/Ch5/S2_RationalNumbers.lean` (rational construction scaffold, 5QA–5QL line)
  - `Set/Ch5/S3_RealNumbers.lean` (Dedekind-cut real-number scaffold, 5RA–5RJ line)
  - `Set/Ch5/S4_Summaries.lean` (algebraic summary interfaces)

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
- `Set/Ch4/S2_PeanosPostulates.lean`
- `Set/Ch4/S3_RecursionOnOmega.lean`
- `Set/Ch4/S4_Arithmetic.lean`
- `Set/Ch4/S5_OrderingOnOmega.lean`
- `Set/Ch4.lean` (aggregator)

- `Set/Ch5/S1_Integers.lean`
- `Set/Ch5/S2_RationalNumbers.lean`
- `Set/Ch5/S3_RealNumbers.lean`
- `Set/Ch5/S4_Summaries.lean`
- `Set/Ch5.lean` (aggregator)

And top-level:

- `Set.lean` now imports `Set.Ch2`, `Set.Ch3`, `Set.Ch4`, and `Set.Ch5`.

## 2) Why AC Is Structured This Way

To keep future “six equivalent forms of AC” development clean:

- AC declarations are kept out of `Set/Axioms.lean` (which only contains core set axioms).
- Canonical AC declarations live in `Set/Choice.lean`, wrapped in a
  `Choice` sub-namespace (`Set.Choice.ChoiceFirstForm`,
  `Set.Choice.choice_first_form`, `Set.Choice.ChoiceSecondForm`).
  Wrapping forces every downstream file to either qualify the name or
  `open Choice`; either way the AC dependency is visible at the use site.
- `Set/Choice.lean` only imports `Set.Ch3.S2_Relations`, so it can be
  imported by `Set/Ch3/S4_Functions.lean` without a circular dependency.
  To make that possible, the AC predicates state "function" inline as
  `IsRelation H ∧ ∀ x ∈ dom H, ∃! y, ⟪x, y⟫ ∈ H` — definitionally equal
  to `IsFunction H`, so consumers destructure it as an `IsFunction`
  directly. This keeps `Set/Choice.lean` as the single home for all six
  forms of AC even though the inductive presentation of AC in Enderton
  spans Chapter 3 (§4 and §5) and Chapter 6.
- AC consumers:
  - `Set/Ch3/S4_Functions.lean` `#check`s the declarations near the top
    (Enderton p.49) and reopens `namespace Choice` at the bottom of the
    file **only** for Theorem 3J(b) — the one declaration whose proof
    actually invokes `choice_first_form`. Theorem 3J(a) and its helpers
    (`LeftInverseRelation`, `one_to_one_preimage_unique`) stay in the
    plain `Set` namespace because they are AC-free. Two `#print axioms`
    lines after the namespace block enforce this split as a build-time
    invariant.
  - `Set/Ch3/S5_InfiniteCartesianProducts.lean` `open`s `Choice` once at
    the top and `#check`s the second-form declaration for the
    infinite-product nonempty theorem.
- Forms are named as separate logical objects (`ChoiceFirstForm`, `ChoiceSecondForm`) so additional forms can be appended naturally:
  - `ChoiceThirdForm`, `ChoiceFourthForm`, ...
- Equivalence proofs can then be added as ordinary theorems between these forms, without changing existing theorem files.

This avoids circular dependencies and allows incremental strengthening without refactoring prior proofs.

## 3) Build Integration

- `Set.lean` now imports chapter aggregators:
  - `Set.Ch2`
  - `Set.Ch3`
  - `Set.Ch4`
  - `Set.Ch5`

So `lake build` (default target `Set`) checks the new formalization modules automatically.

## 4) Axiom Index

- Added `Set/AxiomIndex.md` to record:
  - first textbook appearance (chapter/section/page),
  - declaration location in code.

