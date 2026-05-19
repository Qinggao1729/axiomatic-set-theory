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

## Infinity Axiom (Ch4 §1 site)

Declared in: `Set/Ch4/S1_InductiveSets.lean`

- `infinity` : `∃ A : Set, Inductive A`
  - First appearance: Ch4 §Inductive Sets, p.68
  - Stated in Enderton's literal form because its predicate names
    `∅`, `Successor`, and `Inductive` — all only available once the Ch2
    layer is imported. The declaration is followed by the chosen
    witness `noncomputable def Infinity := Classical.choose infinity`
    and the spec `lemma Infinity.Inductive`.

## Choice and AC-Dependent Assumptions

Canonical declarations live in: `Set/Choice.lean`, under the `Set.Choice`
sub-namespace (so all references go through `open Choice` or full
qualification, which marks AC usage at the call site). `Set/Choice.lean`
is the single intended home for all six equivalent forms of AC
(Chapter 6 will add the remaining four forms and their equivalence
theorems). To allow downstream files in Chapter 3 to import this file
without a circular dependency, the AC predicates state "function"
inline as `IsRelation H ∧ ∀ x ∈ dom H, ∃! y, ⟪x, y⟫ ∈ H` — definitionally
equal to `IsFunction H`.

`Set/Ch3/S4_Functions.lean` `#check`s the declarations at the point
Enderton introduces them (p.49) and reopens `namespace Choice` at the
bottom of the file for Theorem 3J.
`Set/Ch3/S5_InfiniteCartesianProducts.lean` `open`s `Choice` once at the
top for the second-form / infinite-product theorem.

- `Set.Choice.choice_first_form`
  - First appearance: Ch3 §Functions, p.49 (Axiom of Choice, first form)
- `Set.Choice.ChoiceSecondForm` (definition-level formal form)
  - First appearance: Ch3 §Infinite Cartesian Products, p.55
- `Set.thm_3J_a_left_inverse_iff_one_to_one` (proved in
  `Set/Ch3/S4_Functions.lean`; **AC-free** — kept in the plain `Set`
  namespace because its proof does not invoke `choice_first_form`)
  - Enderton: Theorem 3J(a), p.48
- `Set.Choice.thm_3J_b_right_inverse_iff_onto` (proved in
  `Set/Ch3/S4_Functions.lean`; **uses first-form AC** — placed inside
  the `Choice` namespace precisely because the proof invokes
  `choice_first_form`)
  - Enderton: Theorem 3J(b), p.48–49

The split is enforced by two `#print axioms` checks at the bottom of
`Set/Ch3/S4_Functions.lean`: any future edit that accidentally drags AC
into 3J(a), or removes it from 3J(b), will be flagged in the build output.

## Quotient-Compatibility Assumptions

Canonical declarations live in: `Set/Ch3/S6_Equivalence.lean`
(with `Set/Equivalence.lean` kept as compatibility import layer).

- `quotient_function_exists` (proved theorem)
  - Enderton: Theorem 3Q (existence/uniqueness direction), pp.60–61
- `quotient_function_not_exists` (proved theorem)
  - Enderton: Theorem 3Q (non-compatibility direction), pp.60–61

---

Note: AC, quotient-function, and infinity statements live outside
`Set/Axioms.lean` because they depend on higher-level notions
(`IsFunction`, quotient construction, compatibility, `Successor` /
`Inductive`) introduced later in the chapter-structured development.

