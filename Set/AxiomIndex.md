# Axiom Index (Enderton Mapping)

This index records where each axiom first appears in Enderton and where it is
declared in this codebase.

## Core Set Axioms (Centralized)

Declared in: `Set/Axioms.lean`

- `comprehension`
  - First appearance: Ch2 §Axioms, p.21 (Subset axioms / Aussonderung)
- `extensionality`
  - First appearance: Ch2 §Axioms, p.17
- `empty`
  - First appearance: Ch2 §Axioms, p.18
- `pairing`
  - First appearance: Ch2 §Axioms, p.18
- `power`
  - First appearance: Ch2 §Axioms, p.18
- `union_preliminary`
  - First appearance: Ch2 §Axioms, p.18
- `union`
  - First appearance: Ch2 §Arbitrary Unions and Intersections, p.24
- `infinity`
  - First appearance: Ch4 §Inductive Sets, p.68
  - Declared in primitive form in: `Set/Axioms.lean`
  - Enderton-style derived statement (`∃ A, Inductive A`) provided in: `Set/Ch4/S1_InductiveSets.lean`

## Choice and AC-Dependent Assumptions

Canonical declarations live in: `Set/Choice.lean`
(and are cross-referenced in `Set/Ch3/S5_InfiniteCartesianProducts.lean` via `#check`).

- `choice_first_form`
  - First appearance: Ch3 §Functions, p.49 (Axiom of Choice, first form)
- `ChoiceSecondForm` (definition-level formal form)
  - First appearance: Ch3 §Infinite Cartesian Products, p.55
- `left_inverse_iff_one_to_one` (proved theorem)
  - Enderton: Theorem 3J(a), p.48
- `right_inverse_iff_onto` (proved theorem)
  - Enderton: Theorem 3J(b), p.48–49

## Quotient-Compatibility Assumptions

Canonical declarations live in: `Set/Ch3/S6_Equivalence.lean`
(with `Set/Equivalence.lean` kept as compatibility import layer).

- `quotient_function_exists` (proved theorem)
  - Enderton: Theorem 3Q (existence/uniqueness direction), pp.60–61
- `quotient_function_not_exists` (proved theorem)
  - Enderton: Theorem 3Q (non-compatibility direction), pp.60–61

---

Note: AC and quotient-function statements live outside `Set/Axioms.lean`
because they depend on higher-level notions (`IsFunction`, quotient construction,
compatibility) introduced later in the chapter-structured development.

