# Ch3 Section 6 (Equivalence Relations) - Textbook Extraction Draft

Source: Enderton, Chapter 3, pp. 55-62.

## Core Objects and Claims

1. Equivalence-relation primitives on a carrier `A`:
   - reflexive on `A`
   - symmetric
   - transitive
   - binary relation on `A`
2. Theorem 3M:
   - If `R` is a relation and is symmetric + transitive, then `R` is an equivalence relation on `fld R`.
3. Equivalence classes:
   - `[x]_R = { t | xRt }` (implemented with a `ran R` carrier guard).
4. Lemma 3N:
   - For `x, y ∈ A`, `[x]_R = [y]_R ↔ xRy`.
5. Quotient set:
   - `A / R = { [x]_R | x ∈ A }`.
6. Compatibility of a self-map `F : A → A` with `R`.
7. Theorem 3Q:
   - compatible `F` induces unique quotient map `Fq : A/R → A/R`.
   - if not compatible, such quotient map cannot exist.
8. Theorem 3P:
   - equivalence classes form a partition of `A`.

## Mapping to Lean Declarations (Current File)

Primary file: `Set/Ch3/S6_Equivalence.lean`

- `def IsReflexiveOn`
- `def IsSymmetric`
- `def IsTransitiveRel`
- `def IsBinaryRelationOn`
- `def IsEquivalenceRelation`
- `theorem symm_trans_is_equiv`
- `noncomputable def EquivalenceClass`
- `lemma EquivalenceClass.Spec`
- `theorem equiv_class_eq_iff`
- `noncomputable def QuotientSet`
- `lemma QuotientSet.Spec`
- `def IsCompatible`
- `noncomputable def QuotientLift`
- `lemma QuotientLift.Spec`
- `lemma QuotientLift.Pair.Spec`
- `theorem quotient_function_exists`
- `theorem quotient_function_not_exists`
- `def IsPartition`
- `theorem equiv_classes_partition`

## Proof-Flow Notes

- `3M` in Lean requires `IsRelation R` explicitly (to recover ordered-pair witnesses) before proving binary-on-field + reflexive-on-field.
- `3N` uses:
  - forward: `y ∈ [y]_R` from reflexivity, transport membership across class equality.
  - backward: extensionality + symmetry/transitivity to move between classes.
- `3Q` constructive direction:
  - build graph on classes via `QuotientLift`,
  - prove function-ness by compatibility + value uniqueness,
  - prove domain/range are `A / R`.
- `3Q` nonexistence direction:
  - assume induced map exists,
  - use equal classes from `xRy`,
  - force equal outputs by function uniqueness,
  - conclude contradiction with non-compatibility.
- `3P` partition theorem:
  - nonempty block by reflexivity,
  - overlap implies equality via `3N`,
  - coverage by taking class `[x]_R` for each `x ∈ A`.

