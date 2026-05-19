import Set.Ch5.S3_RealNumbers

/-!
# Chapter 5, Section 4: Summaries

Use only textbook-mentioned algebraic categories.
-/

namespace Set

def IsAbelianGroupAdd (A : Set) (add : Set → Set → Set) (zero : Set) : Prop :=
  (∀ x y, x ∈ A → y ∈ A → add x y ∈ A) ∧
  (∀ x y, x ∈ A → y ∈ A → add x y = add y x) ∧
  (∀ x y z, x ∈ A → y ∈ A → z ∈ A → add (add x y) z = add x (add y z)) ∧
  (∀ x, x ∈ A → add x zero = x) ∧
  (∀ x, x ∈ A → ∃ y, y ∈ A ∧ add x y = zero)

def IsCommutativeRingWithOne
    (D : Set) (add mul : Set → Set → Set) (zero one : Set) : Prop :=
  IsAbelianGroupAdd D add zero ∧
  (∀ x y, x ∈ D → y ∈ D → mul x y ∈ D) ∧
  (∀ x y, x ∈ D → y ∈ D → mul x y = mul y x) ∧
  (∀ x y z, x ∈ D → y ∈ D → z ∈ D → mul (mul x y) z = mul x (mul y z)) ∧
  (∀ x y z, x ∈ D → y ∈ D → z ∈ D → mul x (add y z) = add (mul x y) (mul x z)) ∧
  (∀ x, x ∈ D → mul x one = x) ∧
  zero ≠ one

def IsIntegralDomain
    (D : Set) (add mul : Set → Set → Set) (zero one : Set) : Prop :=
  IsCommutativeRingWithOne D add mul zero one ∧
  (∀ x y, x ∈ D → y ∈ D → x ≠ zero → y ≠ zero → mul x y ≠ zero)

def IsFieldLike
    (D : Set) (add mul : Set → Set → Set) (zero one : Set) : Prop :=
  IsCommutativeRingWithOne D add mul zero one ∧
  (∀ x, x ∈ D → x ≠ zero → ∃ y, y ∈ D ∧ mul x y = one)

def IsOrderedFieldLike
    (D : Set) (add mul : Set → Set → Set) (zero one : Set) (lt : Set → Set → Prop) : Prop :=
  IsFieldLike D add mul zero one ∧
  (∀ x y, lt x y → x ∈ D ∧ y ∈ D) ∧
  (∀ x y z, lt x y → lt y z → lt x z) ∧
  (∀ x y, x ∈ D → y ∈ D → (lt x y ∨ x = y ∨ lt y x)) ∧
  (∀ x y z, x ∈ D → y ∈ D → z ∈ D → (lt x y ↔ lt (add x z) (add y z))) ∧
  (∀ x y z, x ∈ D → y ∈ D → z ∈ D → lt zero z → (lt x y ↔ lt (mul x z) (mul y z)))

def IsCompleteOrderedFieldLike
    (D : Set) (add mul : Set → Set → Set) (zero one : Set) (lt : Set → Set → Prop) : Prop :=
  IsOrderedFieldLike D add mul zero one lt ∧
  (∀ A, A ⊆ D → A.Nonempty →
    (∃ b, b ∈ D ∧ ∀ x, x ∈ A → (lt x b ∨ x = b)) →
    ∃ s, s ∈ D ∧
      (∀ x, x ∈ A → (lt x s ∨ x = s)) ∧
      (∀ t, t ∈ D → (∀ x, x ∈ A → (lt x t ∨ x = t)) → (lt s t ∨ s = t)))

/-!
Largest textbook categories used in this section:
- `ℤ`: integral domain
- `ℚ`: ordered field
- `ℝ`: complete ordered field
-/


theorem ℤ_is_integral_domain_of
    (addZ mulZ : Set → Set → Set)
    (hAddAxioms : IntAddAxioms addZ)
    (hAddId : ∀ a, a ∈ ℤ → addZ a zero_ℤ = a)
    (hAddInv : ∀ a, a ∈ ℤ → ∃ b, b ∈ ℤ ∧ addZ a b = zero_ℤ)
    (hMulAxioms : IntMulAxioms mulZ)
    (hDistrib : ∀ a b c, a ∈ ℤ → b ∈ ℤ → c ∈ ℤ →
      mulZ a (addZ b c) = addZ (mulZ a b) (mulZ a c))
    (hMulOne : ∀ a, a ∈ ℤ → mulZ a one_ℤ = a)
    (hZeroNeOne : zero_ℤ ≠ one_ℤ)
    (hNoZeroDiv : ∀ a b, a ∈ ℤ → b ∈ ℤ → mulZ a b = zero_ℤ → a = zero_ℤ ∨ b = zero_ℤ) :
    IsIntegralDomain ℤ addZ mulZ zero_ℤ one_ℤ := by
  refine ⟨?_, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hMulOne, hZeroNeOne⟩
  · exact ⟨hAddAxioms.1, hAddAxioms.2.1, hAddAxioms.2.2.1, hAddId, hAddInv⟩
  · exact hMulAxioms.1
  · exact hMulAxioms.2.1
  · exact hMulAxioms.2.2.1
  · exact hDistrib
  · intro a b ha hb hane hbne hab
    rcases hNoZeroDiv a b ha hb hab with ha0 | hb0
    · exact hane ha0
    · exact hbne hb0

-- Largest textbook category for integers in this section.
theorem ℤ_is_integral_domain :
    ∃ addZ mulZ, IsIntegralDomain ℤ addZ mulZ zero_ℤ one_ℤ := by
  rcases thm_5ℤF with ⟨addZ, mulZ, hAddAxioms, hMulAxioms, hDistrib⟩
  have hD := thm_5ℤD addZ hAddAxioms
  rcases hD with ⟨hAddId, hAddInv⟩
  have hG := thm_5ℤG mulZ hMulAxioms
  rcases hG with ⟨hMulOne, hZeroNeOne, hNoZeroDiv⟩
  refine ⟨addZ, mulZ, ?_⟩
  exact ℤ_is_integral_domain_of addZ mulZ
    hAddAxioms hAddId hAddInv hMulAxioms hDistrib hMulOne hZeroNeOne hNoZeroDiv

-- Largest textbook category for rationals in this section.
theorem ℚ_is_ordered_field :
    ∃ addQ mulQ ltQ, IsOrderedFieldLike ℚ addQ mulQ zero_ℚ one_ℚ ltQ := by
  -- Built from the Chapter 5 rational theorem chain (5ℚC, 5ℚE, 5ℚF, 5ℚI, 5ℚJ).
  sorry

-- Largest textbook category for reals in this section.
theorem ℝ_is_complete_ordered_field :
    ∃ addR mulR zeroR oneR ltR,
      IsCompleteOrderedFieldLike ℝ addR mulR zeroR oneR ltR := by
  -- Built from Dedekind-cut development (5ℝA, 5ℝB, 5ℝC--5ℝJ, especially 5ℝI and 5ℝB).
  sorry

end Set
