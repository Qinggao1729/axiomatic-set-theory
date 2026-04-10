import Set.Ch2.S2_ArbitraryUnionsIntersections
import Set.SimpAttrs

/-!
# Chapter 2, Section 3: Algebra of Sets

This section includes algebraic laws for `∪`, `∩`, `-`, arbitrary unions,
and arbitrary intersections.
-/

namespace Set

/- Commutative laws [Enderton, p. 28] -/
theorem Union.comm (A B : Set) : A ∪ B = B ∪ A := by
  apply extensionality
  intro x
  apply Iff.intro
  repeat
  { intro hx
    simp [Union.Spec] at *
    simpa [or_comm] using hx
  }

theorem Intersection.comm (A B : Set) : A ∩ B = B ∩ A := by
  apply extensionality
  intro x
  apply Iff.intro
  repeat
  { simp [Intersection.Spec]
    intro hxa hxb
    exact And.intro hxb hxa
  }


/- Associative laws [Enderton, p. 28] -/
theorem Union.assoc (A B C : Set) : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
  apply extensionality
  intro x
  apply Iff.intro
  repeat
  { intro hx
    simp [Union.Spec] at *
    simpa [or_assoc] using hx
  }

theorem Intersection.assoc (A B C : Set) : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
  apply extensionality
  intro x
  apply Iff.intro
  simp [Intersection.Spec]
  · intro hxa hxb hxc
    exact And.intro (And.intro hxa hxb) hxc
  · simp [Intersection.Spec]
    intro hxa hxb hxc
    exact And.intro hxa (And.intro hxb hxc)


/- Distributive laws [Enderton, p. 28] -/
theorem Intersection.dist (A B C : Set) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro hx
    simp [Union.Spec, Intersection.Spec] at *
    simp_all
  · intro hx
    simp [Union.Spec, Intersection.Spec] at *
    cases hx with
    | inl hxAB => simp_all
    | inr hxAC => simp_all

theorem Union.dist (A B C : Set) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro hx
    simp [Intersection.Spec, Union.Spec] at *
    cases hx with
    | inl hxA => simp_all
    | inr hxBC => simp_all
  · intro hx
    simp [Intersection.Spec, Union.Spec] at *
    obtain ⟨left, right⟩ := hx
    cases left with
    | inl h =>
      apply Or.intro_left
      exact h
    | inr h_1 =>
      simp_all


/- De Morgan's laws [Enderton, p. 28] -/
theorem Union.deMorgan (A B C : Set) : C - (A ∪ B) = (C - A) ∩ (C - B) := by
  apply extensionality
  intro x
  apply Iff.intro
  repeat
  { intro hx
    simp [Difference.Spec, Intersection.Spec, Union.Spec] at *
    simp_all
  }

theorem Intersection.deMorgan (A B C : Set) : C - (A ∩ B) = (C - A) ∪ (C - B) := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro hx
    simp [Difference.Spec, Intersection.Spec, Union.Spec] at *
    simp_all
    cases Classical.em (x ∈ A) with
      | inl hxa =>
        apply Or.intro_right
        obtain ⟨_, hx₂⟩ := hx
        exact hx₂ hxa
      | inr hnxa =>
        apply Or.intro_left
        exact hnxa
  · intro hx
    simp [Difference.Spec, Intersection.Spec, Union.Spec] at *
    cases hx with
    | inl h => simp_all
    | inr h_1 => simp_all


/- Identities involvoing ∅ [Enderton, p. 28] -/
@[simp]theorem Union.empty (A : Set) : A ∪ ∅ = A := by
  apply extensionality
  intro x
  rw [Union.Spec]
  simp [Empty.Spec]

@[simp] theorem Intersection.empty (A : Set) : A ∩ ∅ = (∅ : Set) := by
  apply extensionality
  intro x
  rw [Intersection.Spec]
  simp [Empty.Spec]

@[simp] theorem Intersection.empty' (A C : Set) : A ∩ (C - A) = (∅ : Set) := by
  apply extensionality
  intro x
  simp_all [Empty.Spec, Difference.Spec, Intersection.Spec]


/- Relative complements under some fixed space `S ⊇ A` [Enderton, p. 28-29] -/
/- (textbook abbreviation `-A := S - A`) -/

theorem Union.space (A S : Set) (hAS : A ⊆ S) : A ∪ S = S := by
  apply extensionality
  intro x
  constructor
  · intro hx
    simp_all only [SubsetOf, Spec]
    cases hx with
    | inl hxA => exact hAS x hxA
    | inr hxS => exact hxS
  · intro hxS
    simp_all only [SubsetOf, Spec]
    simp []

theorem Intersection.space (A S : Set) (hAS : A ⊆ S) : A ∩ S = A := by
  apply extensionality
  intro x
  constructor
  · intro hx
    simp_all only [Intersection.Spec]
  · intro hxA
    simp_all [SubsetOf, Intersection.Spec]

theorem Union.compl (A S : Set) (hAS : A ⊆ S) : A ∪ (S - A) = S := by
  apply extensionality
  intro x
  constructor
  · intro hx
    simp_all only [SubsetOf, Spec, Difference.Spec]
    cases hx with
    | inl hxA => exact hAS x hxA
    | inr hx => exact hx.1
  · intro hxS
    simp_all [SubsetOf, Spec, Difference.Spec]
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr hxA

theorem Intersection.compl (A S : Set) : A ∩ (S - A) = (∅ : Set) := by
  simp [Intersection.empty' A S]


/- Monotonicity and antimonotonicity [Enderton, p. 29] -/
theorem Union.mono (A B C : Set) : A ⊆ B → A ∪ C ⊆ B ∪ C := by
  intro hAB x hx
  specialize hAB x
  simp_all only [Spec]
  cases hx with
  | inl h => simp_all
  | inr h => simp_all

theorem Intersection.mono (A B C : Set) : A ⊆ B → A ∩ C ⊆ B ∩ C := by
  intro hAB x hx
  specialize hAB x
  simp_all [Spec]

theorem BigUnion.mono (A B : Set) : A ⊆ B → ⋃A ⊆ ⋃B := by
  intro hAB x hx
  rcases (BigUnion.Spec).mp hx with ⟨a, haA, hxa⟩
  exact (BigUnion.Spec).mpr ⟨a, hAB a haA, hxa⟩

theorem Difference.antimono (A B C : Set) : A ⊆ B → C - B ⊆ C - A := by
  intro hAB x hx
  simp [Difference.Spec] at hx ⊢
  constructor
  · exact hx.1
  · intro hxA
    exact hx.2 (hAB x hxA)

theorem BigIntersection.antimono_nonempty (A B : Set) (hA : A.Nonempty) (hB : B.Nonempty) :
    A ⊆ B → BigIntersection B hB ⊆ BigIntersection A hA := by
  intro hAB x hx
  rw [BigIntersection.Spec hB] at hx
  rw [BigIntersection.Spec hA]
  intro a ha
  exact hx a (hAB a ha)


/- `{A ∪ X | X ∈ ℬ}` [Enderton, p. 30] -/
noncomputable def FamilyUnion (A ℬ : Set) : Set :=
  Comprehension
    (λ t ↦ ∃ X : Set, X ∈ ℬ ∧ t = A ∪ X)
    (𝒫 (A ∪ ⋃ℬ))

@[simp]lemma FamilyUnion.Spec {A ℬ t : Set} :
    t ∈ FamilyUnion A ℬ ↔ t ∈ 𝒫 (A ∪ ⋃ℬ) ∧ ∃ X : Set, X ∈ ℬ ∧ t = A ∪ X := by
  simp [FamilyUnion, Comprehension.Spec]
attribute [set_spec_simps] FamilyUnion.Spec

theorem FamilyUnion.nonempty (A ℬ : Set) (hℬ : ℬ.Nonempty) : (FamilyUnion A ℬ).Nonempty := by
  obtain ⟨X, hX⟩ := hℬ
  refine ⟨A ∪ X, ?_⟩
  refine (FamilyUnion.Spec).2 ?_
  constructor
  · rw [Power.Spec]
    intro t ht
    rw [Union.Spec] at ht ⊢
    cases ht with
    | inl htA => exact Or.inl htA
    | inr htX =>
        apply Or.inr
        rw [BigUnion.Spec]
        exact ⟨X, hX, htX⟩
  · exact ⟨X, hX, rfl⟩

/- `{A ∩ X | X ∈ ℬ}` [Enderton, p. 30] -/
noncomputable def FamilyInter (A ℬ : Set) : Set :=
  Comprehension
    (λ t ↦ ∃ X : Set, X ∈ ℬ ∧ t = A ∩ X)
    (𝒫 A)

@[simp]lemma FamilyInter.Spec {A ℬ t : Set} :
    t ∈ FamilyInter A ℬ ↔ t ∈ 𝒫 A ∧ ∃ X : Set, X ∈ ℬ ∧ t = A ∩ X := by
  simp [FamilyInter, Comprehension.Spec]
attribute [set_spec_simps] FamilyInter.Spec

/- Generalized distributive law [Enderton, p. 30] -/
/- `A ∪ ⋂ ℬ = ⋂ {A ∩ X | X ∈ ℬ}` for `ℬ ≠ ∅` -/
theorem Union.dist_biginter (A ℬ : Set) (hℬ : ℬ.Nonempty) :
    A ∪ BigIntersection ℬ hℬ = BigIntersection (FamilyUnion A ℬ) (FamilyUnion.nonempty A ℬ hℬ) := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro hx
    rw [BigIntersection.Spec]
    intro t ht
    rw [FamilyUnion.Spec] at ht
    rcases ht with ⟨_, ⟨X, hX, rfl⟩⟩
    rw [Union.Spec] at hx ⊢
    cases hx with
    | inl hxa => exact Or.inl hxa
    | inr hxI =>
      rw [BigIntersection.Spec] at hxI
      exact Or.inr (hxI X hX)
  · intro hx
    rw [Union.Spec]
    by_cases hxa : x ∈ A
    · exact Or.inl hxa
    · right
      rw [BigIntersection.Spec]
      intro Y hY
      have hAY : A ∪ Y ∈ FamilyUnion A ℬ := by
        rw [FamilyUnion.Spec]
        constructor
        · rw [Power.Spec]
          rw [Union.comm A Y, Union.comm A (⋃ℬ)]
          apply Union.mono Y (⋃ℬ) A
          apply member_subset_bigUnion
          exact hY
        · exact ⟨Y, hY, rfl⟩
      rw [BigIntersection.Spec] at hx
      have hxAY : x ∈ A ∪ Y := hx (A ∪ Y) hAY
      rw [Union.Spec] at hxAY
      cases hxAY with
      | inl hxa' => exact False.elim (hxa hxa')
      | inr hxY => exact hxY

/- A ∩ ⋃ℬ = ⋃{A ∩ X | X ∈ ℬ} -/
theorem Intersection.dist_bigunion (A ℬ : Set) :
    A ∩ ⋃ℬ = ⋃(FamilyInter A ℬ) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rw [Intersection.Spec, BigUnion.Spec] at hx
    rcases hx with ⟨hxA, ⟨X, hX, hxX⟩⟩
    rw [BigUnion.Spec]
    refine ⟨A ∩ X, ?_, ?_⟩
    · rw [FamilyInter.Spec]
      constructor
      · rw [Power.Spec]
        intro t ht
        rw [Intersection.Spec] at ht
        exact ht.left
      · exact ⟨X, hX, rfl⟩
    · rw [Intersection.Spec]
      exact ⟨hxA, hxX⟩
  · intro hx
    rw [BigUnion.Spec] at hx
    rcases hx with ⟨t, htFam, hxt⟩
    rw [FamilyInter.Spec] at htFam
    rcases htFam with ⟨_, ⟨X, hX, rfl⟩⟩
    rw [Intersection.Spec] at hxt ⊢
    constructor
    · exact hxt.left
    · rw [BigUnion.Spec]
      exact ⟨X, hX, hxt.right⟩

/- `{C - X | X ∈ 𝒜}` [Enderton, p. 31] -/
noncomputable def FamilyDiff (C 𝒜 : Set) : Set :=
  Comprehension
    (λ t ↦ ∃ X : Set, X ∈ 𝒜 ∧ t = C - X)
    (𝒫 C)

@[simp] lemma FamilyDiff.Spec {C 𝒜 t : Set} :
    t ∈ FamilyDiff C 𝒜 ↔ t ∈ 𝒫 C ∧ ∃ X : Set, X ∈ 𝒜 ∧ t = C - X := by
  simp [FamilyDiff, Comprehension.Spec]
attribute [set_spec_simps] FamilyDiff.Spec

theorem FamilyDiff.nonempty (C 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) : (FamilyDiff C 𝒜).Nonempty := by
  obtain ⟨X, hX⟩ := h𝒜
  refine ⟨C - X, ?_⟩
  rw [FamilyDiff.Spec]
  constructor
  · rw [Power.Spec]
    intro t ht
    rw [Difference.Spec] at ht
    exact ht.1
  · exact ⟨X, hX, rfl⟩

/- `C - ⋃𝒜 = ⋂{C - X | X ∈ 𝒜}` for `𝒜 ≠ ∅` -/
theorem deMorgan_bigunion (C 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) :
    C - ⋃𝒜 = BigIntersection (FamilyDiff C 𝒜) (FamilyDiff.nonempty C 𝒜 h𝒜) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    simp_all only [set_spec_simps]
    intro t ht
    rcases ht with ⟨_, ⟨X, hX, rfl⟩⟩
    rw [Difference.Spec]
    constructor
    · exact hx.1
    · intro hxX
      apply hx.2
      have hxU : ∃ b : Set, b ∈ 𝒜 ∧ x ∈ b := ⟨X, hX, hxX⟩
      simpa only [set_spec_simps] using hxU
  · intro hx
    have hDiffInFamily : ∀ Y : Set, Y ∈ 𝒜 → C - Y ∈ FamilyDiff C 𝒜 := by
      intro Y hY
      simp_all only [set_spec_simps]
      constructor
      · intro t ht
        rw [Difference.Spec] at ht
        exact ht.1
      · exact ⟨Y, hY, rfl⟩
    simp_all only [set_spec_simps]
    constructor
    · obtain ⟨X, hX⟩ := h𝒜
      have hxCX : x ∈ C - X := hx (C - X) (hDiffInFamily X hX)
      rw [Difference.Spec] at hxCX
      exact hxCX.1
    · intro hxU
      have hxU' : ∃ b : Set, b ∈ 𝒜 ∧ x ∈ b := by
        simpa only [set_spec_simps] using hxU
      rcases hxU' with ⟨Y, hY, hxY⟩
      have hxCY : x ∈ C - Y := hx (C - Y) (hDiffInFamily Y hY)
      rw [Difference.Spec] at hxCY
      exact hxCY.2 hxY

/- `C - ⋂𝒜 = ⋃{C - X | X ∈ 𝒜}` for `𝒜 ≠ ∅` -/
theorem deMorgan_biginter (C 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) :
    C - BigIntersection 𝒜 h𝒜 = ⋃(FamilyDiff C 𝒜) := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rw [Difference.Spec] at hx
    have hWitness : ∃ X : Set, X ∈ 𝒜 ∧ x ∉ X := by
      by_contra hNo
      have hxI : x ∈ BigIntersection 𝒜 h𝒜 := by
        rw [BigIntersection.Spec]
        simp [] at hNo
        exact hNo
      exact hx.2 hxI
    simp_all only [set_spec_simps]
    rcases hWitness with ⟨X, hX, hxX⟩
    refine ⟨C - X, ?_, ?_⟩
    · constructor
      · intro t ht
        simp_all only [set_spec_simps]
      · exact ⟨X, hX, rfl⟩
    · rw [Difference.Spec]
      exact ⟨hx.1, hxX⟩
  · intro hx
    simp_all only [set_spec_simps]
    rcases hx with ⟨t, htFam, hxt⟩
    rcases htFam with ⟨_, ⟨X, hX, rfl⟩⟩
    rw [Difference.Spec] at hxt
    constructor
    · exact hxt.1
    · intro hxI
      have hxAll : ∀ a : Set, a ∈ 𝒜 → x ∈ a := by
        simpa only [set_spec_simps] using hxI
      exact hxt.2 (hxAll X hX)

end Set
