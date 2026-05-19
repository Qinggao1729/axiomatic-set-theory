import Set.Ch3.S6_Equivalence

/-!
# Chapter 3, Section 7: Ordering Relations

Linear-order definitions and 3R-style consequences.
-/

namespace Set

def TrichotomyOn (R A : Set) : Prop :=
  ∀ x y, x ∈ A → y ∈ A →
    (⟪x, y⟫ ∈ R ∨ x = y ∨ ⟪y, x⟫ ∈ R) ∧
    ¬(⟪x, y⟫ ∈ R ∧ x = y) ∧
    ¬(⟪x, y⟫ ∈ R ∧ ⟪y, x⟫ ∈ R) ∧
    ¬(x = y ∧ ⟪y, x⟫ ∈ R)

def IsLinearOrder (R A : Set) : Prop :=
  IsBinaryRelationOn R A ∧ IsTransitiveRel R ∧ TrichotomyOn R A

theorem linear_order_irreflexive (R A : Set) :
    IsLinearOrder R A → ∀ x, x ∈ A → ⟪x, x⟫ ∉ R := by
  intro hLin x hxA hxR
  rcases hLin with ⟨_, _, hTri⟩
  rcases hTri x x hxA hxA with ⟨_, hNoEq, _, _⟩
  exact hNoEq ⟨hxR, rfl⟩

theorem linear_order_connected (R A : Set) :
    IsLinearOrder R A → ∀ x y, x ∈ A → y ∈ A → x ≠ y → (⟪x, y⟫ ∈ R ∨ ⟪y, x⟫ ∈ R) := by
  intro hLin x y hxA hyA hxy
  rcases hLin with ⟨_, _, hTri⟩
  rcases hTri x y hxA hyA with ⟨hOne, _, _, _⟩
  rcases hOne with hxyR | hEq | hyxR
  · exact Or.inl hxyR
  · exfalso
    exact hxy hEq
  · exact Or.inr hyxR

end Set
