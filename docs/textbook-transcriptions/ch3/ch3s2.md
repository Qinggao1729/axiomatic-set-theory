# Ch3S2 Textbook Extraction (Relations, pp. 39-41)

## Core items mapped to Lean

1. Relation
   - Set theory: `R` is a relation iff every member of `R` is an ordered pair.
   - Lean: `def IsRelation (R : Set) : Prop := ∀ w, w ∈ R → ∃ x y, w = ⟪x, y⟫`

2. Domain / Range / Field
   - Set theory:
     - `dom R = { x | ∃ y, ⟨x, y⟩ ∈ R }`
     - `ran R = { y | ∃ x, ⟨x, y⟩ ∈ R }`
     - `fld R = dom R ∪ ran R`
   - Lean:
     - `Relation.Domain`, `Relation.Domain.Spec`
     - `Relation.Range`, `Relation.Range.Spec`
     - `Relation.Field`, `Relation.Field.Spec`

3. Lemma 3D
   - Set theory: `⟨x, y⟩ ∈ A -> x ∈ ⋃⋃A ∧ y ∈ ⋃⋃A`.
   - Lean: `lemma OrderedPair.in_union_union ...`
   - Human sketch:
     - From `⟨x, y⟩ = { {x}, {x, y} } ∈ A`, we get `{x, y} ∈ ⋃A`.
     - Then `x, y ∈ {x, y}` implies `x, y ∈ ⋃⋃A`.

