import Set.Ch3.S1_OrderedPairs

/-!
# Chapter 3, Section 2: Relations

Relation definitions and basic lemmas (domain/range/field, 3D, etc).
-/

namespace Set


-- Relation [Enderton, p.40]
def IsRelation (R : Set) : Prop :=
  ∀ w, w ∈ R → ∃ x y, w = ⟪x, y⟫

/- [Enderton, Lemma 3D, p.41] -/
lemma OrderedPair.in_union_union (x y A : Set) :
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

/- Domain [Enderton, p.40] -/
noncomputable def Relation.Domain (R : Set) : Set :=
  Comprehension (fun x ↦ ∃ (y : Set), ⟪x, y⟫ ∈ R) (⋃⋃R)

/- [Enderton, p.41] -/
@[simp]
lemma Relation.Domain.Spec {R x : Set} : x ∈ Relation.Domain R ↔ ∃ y, ⟪x, y⟫ ∈ R := by
  rw [Relation.Domain, Comprehension.Spec]
  constructor
  · intro hx
    exact hx.2
  · intro hx
    rcases hx with ⟨y, hxyR⟩
    have hxUnion : x ∈ ⋃⋃R := (OrderedPair.in_union_union x y R hxyR).1
    exact ⟨hxUnion, ⟨y, hxyR⟩⟩
attribute [set_spec_simps] Relation.Domain.Spec
notation:90 "dom " R => Relation.Domain R

/- Domain [Enderton, p.40] -/
noncomputable def Relation.Range (R : Set) : Set :=
  Comprehension (fun y ↦ ∃ (x : Set), ⟪x, y⟫ ∈ R) (⋃⋃R)

/- [Enderton, p.41] -/
@[simp]
lemma Relation.Range.Spec {R y : Set} : y ∈ Relation.Range R ↔ ∃ x, ⟪x, y⟫ ∈ R := by
  rw [Relation.Range, Comprehension.Spec]
  constructor
  · intro hy
    exact hy.2
  · intro hy
    rcases hy with ⟨x, hxyR⟩
    have hyUnion : y ∈ ⋃⋃R := (OrderedPair.in_union_union x y R hxyR).2
    exact ⟨hyUnion, ⟨x, hxyR⟩⟩
attribute [set_spec_simps] Relation.Range.Spec
notation:90 "ran " R => Relation.Range R

/- Field [Enderton, p.40] -/
noncomputable def Relation.Field (R : Set) : Set := (dom R) ∪ (ran R)

@[simp]
lemma Relation.Field.Spec {R z : Set} : z ∈ Relation.Field R ↔ z ∈ (dom R) ∨ z ∈ (ran R) := by
  simp only [Field, Union.Spec, Domain.Spec, Range.Spec]
attribute [set_spec_simps] Relation.Field.Spec
notation:90 "fld " R => Relation.Field R

end Set
