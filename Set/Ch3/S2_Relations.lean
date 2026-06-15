import Set.Ch3.S1_OrderedPairs

/-!
# Chapter 3, Section 2: Relations

Relation definitions and basic lemmas (domain/range/field, 3D, etc).
-/

namespace Set


/-- [Enderton Ch3 §2, p.40] "A *relation* is a set of ordered pairs." -/
def IsRelation (R : Set) : Prop :=
  ∀ w, w ∈ R → ∃ x y, w = ⟪x, y⟫

/-- [Enderton Ch3 §2, p.41] "Lemma 3D If `⟨x, y⟩ ∈ A`, then `x` and `y` belong to `⋃⋃A`." -/
lemma lem_3D_ordered_pair_in_union_union (x y A : Set) :
  ⟪x, y⟫ ∈ A → x ∈ ⋃⋃A ∧ y ∈ ⋃⋃A := by
  intro hxyA
  have hPairMemUnionA : {x, y} ∈ ⋃ A := by
    rw [BigUnion.Spec]
    refine ⟨OrderedPair x y, hxyA, ?_⟩
    simp [OrderedPair.Spec]
  constructor
  · rw [BigUnion.Spec]
    refine ⟨{x, y}, hPairMemUnionA, ?_⟩
    simp [Pair.Spec]
  · rw [BigUnion.Spec]
    refine ⟨{x, y}, hPairMemUnionA, ?_⟩
    simp [Pair.Spec]

/-- [Enderton Ch3 §2, p.41] "Lemma 3D If `⟨x, y⟩ ∈ A`, then `x` and `y` belong to `⋃⋃A`."
(Compatibility alias of `lem_3D_ordered_pair_in_union_union`.) -/
lemma OrderedPair.in_union_union (x y A : Set) :
  ⟪x, y⟫ ∈ A → x ∈ ⋃⋃A ∧ y ∈ ⋃⋃A :=
  lem_3D_ordered_pair_in_union_union x y A


-- Note: Enderton defines domain, range, and field on any sets, not just relations.
-- So if you apply Enderton's formula for dom A to a set that contains a mix of ordered pairs and other random elements,
-- the formula simply ignores the non-pair elements, because they cannot satisfy the condition ∃ y, ⟨x,y⟩ ∈ A.
/-- [Enderton Ch3 §2, p.40] "We define the *domain* of `R` (dom `R`) ... by
`x ∈ dom R ⇔ ∃y ⟨x, y⟩ ∈ R`." -/
noncomputable def Domain (R : Set) : Set :=
  Comprehension (fun x ↦ ∃ (y : Set), ⟪x, y⟫ ∈ R) (⋃⋃R)

/-- [Enderton Ch3 §2, pp.40-41] "`x ∈ dom R ⇔ ∃y ⟨x, y⟩ ∈ R`." -/
@[simp]
lemma Domain.Spec {R x : Set} : x ∈ Domain R ↔ ∃ y, ⟪x, y⟫ ∈ R := by
  rw [Domain, Comprehension.Spec]
  constructor
  · intro hx
    exact hx.2
  · intro hx
    rcases hx with ⟨y, hxyR⟩
    have hxUnion : x ∈ ⋃⋃R := (lem_3D_ordered_pair_in_union_union x y R hxyR).1
    exact ⟨hxUnion, ⟨y, hxyR⟩⟩
attribute [set_spec_simps] Domain.Spec
notation:90 "dom " R => Domain R

lemma Relation.Pair.mem_dom (R x y : Set) : ⟪x, y⟫ ∈ R → x ∈ dom R := by
  intro h
  exact (Domain.Spec).2 ⟨y, h⟩

/-- [Enderton Ch3 §2, p.40] "We define ... the *range* of `R` (ran `R`) ... by
`x ∈ ran R ⇔ ∃t ⟨t, x⟩ ∈ R`." -/
noncomputable def Range (R : Set) : Set :=
  Comprehension (fun y ↦ ∃ (x : Set), ⟪x, y⟫ ∈ R) (⋃⋃R)

/-- [Enderton Ch3 §2, pp.40-41] "`x ∈ ran R ⇔ ∃t ⟨t, x⟩ ∈ R`." -/
@[simp]
lemma Range.Spec {R y : Set} : y ∈ Range R ↔ ∃ x, ⟪x, y⟫ ∈ R := by
  rw [Range, Comprehension.Spec]
  constructor
  · intro hy
    exact hy.2
  · intro hy
    rcases hy with ⟨x, hxyR⟩
    have hyUnion : y ∈ ⋃⋃R := (lem_3D_ordered_pair_in_union_union x y R hxyR).2
    exact ⟨hyUnion, ⟨x, hxyR⟩⟩
attribute [set_spec_simps] Range.Spec
notation:90 "ran " R => Range R

lemma Relation.Pair.mem_ran (R x y : Set) : ⟪x, y⟫ ∈ R → y ∈ ran R := by
  intro h
  exact (Range.Spec).2 ⟨x, h⟩

/-- [Enderton Ch3 §2, p.40] "We define ... the *field* of `R` (fld `R`) by
`fld R = dom R ∪ ran R`." -/
noncomputable def Field (R : Set) : Set := (dom R) ∪ (ran R)

@[simp]
lemma Field.Spec {R z : Set} : z ∈ Field R ↔ z ∈ (dom R) ∨ z ∈ (ran R) := by
  simp only [Field, Union.Spec, Domain.Spec, Range.Spec]
attribute [set_spec_simps] Field.Spec
notation:90 "fld " R => Field R

end Set
