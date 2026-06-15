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

## Infinity Axiom (Primitive + Derived Enderton Form)

Declared primitive axiom in: `Set/Axioms.lean`

- `infinity` :
  `∃ A, (∃ e, (∀ x, x ∉ e) ∧ e ∈ A) ∧ (∀ a, a ∈ A → ∃ s, (∀ x, x ∈ s ↔ x ∈ a ∨ x = a) ∧ s ∈ A)`
  - First appearance: Ch4 §Inductive Sets, p.68 (textbook statement in shorthand)

Derived Enderton-style theorem in: `Set/Ch4/S1_InductiveSets.lean`

- `infinity_inductive : ∃ A, Inductive A`
  - Obtained from the primitive witness form, then used for
    `noncomputable def Infinity := Classical.choose infinity_inductive`
    and `lemma Infinity.Inductive`.

## Choice and AC-Dependent Assumptions

First-form AC is declared in-place in
`Set/Ch3/S4_Functions.lean`:

- `Set.ChoiceFirstForm` (AC-free logical form, plain `Set`)
- `Set.Choice.choice_first_form` (axiom, in a short `namespace Choice` block)

Form II (multiplicative / infinite-product form) is likewise defined in-place
in `Set/Ch3/S5_InfiniteCartesianProducts.lean` as `Set.ChoiceSecondForm`,
with the axiom and AC-dependent consequences in `Set.Choice`.

`Set/Choice.lean` keeps shared AC infrastructure and non-local forms
(III/IV/VI), using inline function predicates
`IsRelation H ∧ ∀ x ∈ dom H, ∃! y, ⟪x, y⟫ ∈ H`.

`Set/Ch3/S4_Functions.lean` `#check`s first-form declarations at Enderton's
introduction point (p.49) and reopens `namespace Choice` again at the bottom
for Theorem 3J(b).
`Set/Ch3/S5_InfiniteCartesianProducts.lean` defines AC form II in plain
`Set` (AC-free statement/equivalence), then enters `Set.Choice` for the
axiom declaration and AC-dependent consequences.

- `Set.Choice.choice_first_form`
  - First appearance: Ch3 §Functions, p.49 (Axiom of Choice, first form)
- `Set.ChoiceSecondForm` (defined in
  `Set/Ch3/S5_InfiniteCartesianProducts.lean`)
  - First appearance: Ch3 §Infinite Cartesian Products, p.55
- `Set.thm_3Ja_left_inverse_iff_one_to_one` (proved in
  `Set/Ch3/S4_Functions.lean`; **AC-free** — kept in the plain `Set`
  namespace because its proof does not invoke `choice_first_form`)
  - Enderton: Theorem 3J(a), p.48
- `Set.Choice.thm_3Jb_right_inverse_iff_onto` (proved in
  `Set/Ch3/S4_Functions.lean`; **uses first-form AC** — placed inside
  the `Choice` namespace precisely because the proof invokes
  `choice_first_form`)
  - Enderton: Theorem 3J(b), p.48–49

The split is enforced by two `#print axioms` checks at the bottom of
`Set/Ch3/S4_Functions.lean`: any future edit that accidentally drags AC
into 3J(a), or removes it from 3J(b), will be flagged in the build output.

## Quotient-Compatibility Assumptions

Canonical declarations live in: `Set/Ch3/S6_Equivalence.lean`.

- `thm_3Q_compatible_exists_unique_quotient_map` (proved theorem)
  - Enderton: Theorem 3Q (existence/uniqueness direction), pp.60–61
- `thm_3Q_incompatible_not_exists_quotient_map` (proved theorem)
  - Enderton: Theorem 3Q (non-compatibility direction), pp.60–61

---

Note: AC and quotient-function statements live outside `Set/Axioms.lean`
because they depend on higher-level notions (`IsFunction`, quotient
construction, compatibility) introduced later in the chapter-structured
development.

