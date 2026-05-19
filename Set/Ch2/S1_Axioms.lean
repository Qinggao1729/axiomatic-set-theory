import Aesop
import Mathlib.Logic.Basic
import Set.Axioms
import Set.SimpAttrs

/-!
# Chapter 2, Section 1: Axioms

This section checks the primitive axioms from `Set/Axioms.lean`,
then develops immediate constructions and consequences (e.g. `∅` and uniqueness).
-/

namespace Set

-- **Extensionality axiom** [Enderton, p. 17]
#check extensionality


-- **Empty set** [Enderton, p. 18]
#check empty

noncomputable def Empty : Set := Classical.choose empty

@[simp] lemma Empty.Spec {x : Set} : x ∉ Empty :=
  (Classical.choose_spec empty) x
attribute [set_spec_simps] Empty.Spec

-- Every empty set is equal to `∅` (empty set uniqueness in definitional form).
theorem empty_eq_empty (A : Set) (hA : ∀ x : Set, x ∉ A) : A = Empty := by
  apply extensionality
  intro x
  constructor
  · intro hx
    exact False.elim (hA x hx)
  · intro hx
    exact False.elim (Empty.Spec hx)

theorem empty_unique : ∃! B : Set, ∀ x : Set, x ∉ B := by
  refine ⟨Empty, ?_, ?_⟩
  · intro x
    exact Empty.Spec
  intro B hB
  exact empty_eq_empty B hB

notation "∅" => Empty


-- **Pairing axiom** [Enderton, p. 18]
#check pairing

noncomputable def Pair (u v : Set) : Set := Classical.choose (pairing u v)
notation:max "{" x ", " y "}" => Pair x y

@[simp] lemma Pair.Spec {u v x : Set} : x ∈ Pair u v ↔ x = u ∨ x = v :=
  (Classical.choose_spec (pairing u v)) x
attribute [set_spec_simps] Pair.Spec

-- Any set with the pair-membership specification is equal to `Pair u v`.
theorem pair_eq_pair (u v A : Set)
    (hA : ∀ x : Set, x ∈ A ↔ x = u ∨ x = v) : A = Pair u v := by
  apply extensionality
  intro x
  have hAspec : x ∈ A ↔ x = u ∨ x = v := hA x
  have hPspec : x ∈ Pair u v ↔ x = u ∨ x = v := Pair.Spec
  simp only [hAspec, hPspec]

theorem pair_unique (u v : Set) :
    ∃! B : Set, ∀ x : Set, x ∈ B ↔ x = u ∨ x = v := by
  refine ⟨Pair u v, ?_, ?_⟩
  · intro x
    exact Pair.Spec
  intro B hB
  exact pair_eq_pair u v B hB


-- **Singleton** [Enderton, p. 19]
noncomputable def Singleton (x : Set) : Set := Classical.choose (pairing x x)
notation:max "{" x "}" => Singleton x

@[simp] lemma Singleton.Spec {x y : Set} : y ∈ Singleton x ↔ y = x := by
  have hSingletonSpec : y ∈ Singleton x ↔ y = x ∨ y = x :=
    Classical.choose_spec (pairing x x) y
  simp only [hSingletonSpec, or_self]
attribute [set_spec_simps] Singleton.Spec


-- **Power set** [Enderton, p. 18]
#check power

noncomputable def Power (A : Set) : Set := Classical.choose (power A)

@[simp] lemma Power.Spec {A x : Set} : x ∈ Power A ↔ x ⊆ A :=
  (Classical.choose_spec (power A)) x
attribute [set_spec_simps] Power.Spec

-- Any set with the power-set membership specification is equal to `Power A`.
theorem power_eq_power (A B : Set)
    (hB : ∀ x : Set, x ∈ B ↔ x ⊆ A) : B = Power A := by
  apply extensionality
  intro x
  have hBspec : x ∈ B ↔ x ⊆ A := hB x
  have hPspec : x ∈ Power A ↔ x ⊆ A := Power.Spec
  simp only [hBspec, hPspec]

theorem power_unique (A : Set) :
    ∃! B : Set, ∀ x : Set, x ∈ B ↔ x ⊆ A := by
  refine ⟨Power A, ?_, ?_⟩
  · intro x
    exact Power.Spec
  intro B hB
  exact power_eq_power A B hB

prefix:75 "𝒫" => Power


-- **Binary union** [Enderton, p. 18]
#check union_preliminary

noncomputable def Union (A B : Set) : Set := Classical.choose (union_preliminary A B)

@[simp] lemma Union.Spec {A B x : Set} : x ∈ Union A B ↔ x ∈ A ∨ x ∈ B :=
  (Classical.choose_spec (union_preliminary A B)) x
attribute [set_spec_simps] Union.Spec

theorem union_eq_union (A B U : Set)
    (hU : ∀ x : Set, x ∈ U ↔ x ∈ A ∨ x ∈ B) : U = Union A B := by
  apply extensionality
  intro x
  have hUspec : x ∈ U ↔ x ∈ A ∨ x ∈ B := hU x
  have hUnionSpec : x ∈ Union A B ↔ x ∈ A ∨ x ∈ B := Union.Spec
  simp only [hUspec, hUnionSpec]

theorem union_unique (A B : Set) :
    ∃! U : Set, ∀ x : Set, x ∈ U ↔ x ∈ A ∨ x ∈ B := by
  refine ⟨Union A B, ?_, ?_⟩
  · intro x
    exact Union.Spec
  intro U hU
  exact union_eq_union A B U hU

infix:70 " ∪ " => Union


-- **Subset axioms / comprehension schema** [Enderton, p. 21]
#check comprehension

noncomputable def Comprehension (P : Set → Prop) (c : Set) : Set :=
  Classical.choose (comprehension P c)

@[simp] lemma Comprehension.Spec {P : Set → Prop} {c x : Set} :
    x ∈ Comprehension P c ↔ x ∈ c ∧ P x := by
  rw [Comprehension]
  exact (Classical.choose_spec (comprehension P c)) x
attribute [set_spec_simps] Comprehension.Spec

-- Any set with the comprehension specification is equal to `Comprehension P c`.
theorem comprehension_eq_comprehension (P : Set → Prop) (c C : Set)
    (hC : ∀ x : Set, x ∈ C ↔ x ∈ c ∧ P x) : C = Comprehension P c := by
  apply extensionality
  intro x
  have hCspec : x ∈ C ↔ x ∈ c ∧ P x := hC x
  have hComprehensionSpec : x ∈ Comprehension P c ↔ x ∈ c ∧ P x := Comprehension.Spec
  simp only [hCspec, hComprehensionSpec]

theorem comprehension_unique (P : Set → Prop) (c : Set) :
    ∃! C : Set, ∀ x : Set, x ∈ C ↔ x ∈ c ∧ P x := by
  refine ⟨Comprehension P c, ?_, ?_⟩
  · intro x
    exact Comprehension.Spec
  intro C hC
  exact comprehension_eq_comprehension P c C hC


-- **Binary intersection** [Enderton, p. 21]
noncomputable def Intersection (A B : Set) : Set :=
  Comprehension (fun x => x ∈ B) A

@[simp] lemma Intersection.Spec {A B x : Set} : x ∈ Intersection A B ↔ x ∈ A ∧ x ∈ B := by
  simp [Intersection, Comprehension.Spec]
attribute [set_spec_simps] Intersection.Spec

-- Any set with the intersection specification is equal to `Intersection A B`.
theorem intersection_eq_intersection (A B I : Set)
    (hI : ∀ x : Set, x ∈ I ↔ x ∈ A ∧ x ∈ B) : I = Intersection A B := by
  apply extensionality
  intro x
  have hIspec : x ∈ I ↔ x ∈ A ∧ x ∈ B := hI x
  have hIntersectionSpec : x ∈ Intersection A B ↔ x ∈ A ∧ x ∈ B := Intersection.Spec
  simp only [hIspec, hIntersectionSpec]

theorem intersection_unique (A B : Set) :
    ∃! I : Set, ∀ x : Set, x ∈ I ↔ x ∈ A ∧ x ∈ B := by
  refine ⟨Intersection A B, ?_, ?_⟩
  · intro x
    exact Intersection.Spec
  intro I hI
  exact intersection_eq_intersection A B I hI

infix:70 " ∩ " => Intersection


-- **Relative complement** [Enderton, p. 21]
noncomputable def Difference (A B : Set) : Set :=
  Comprehension (fun x => x ∉ B) A

@[simp] lemma Difference.Spec {A B x : Set} : x ∈ Difference A B ↔ x ∈ A ∧ x ∉ B := by
  simp [Difference, Comprehension.Spec]
attribute [set_spec_simps] Difference.Spec

-- Any set with the difference specification is equal to `Difference A B`.
theorem difference_eq_difference (A B D : Set)
    (hD : ∀ x : Set, x ∈ D ↔ x ∈ A ∧ x ∉ B) : D = Difference A B := by
  apply extensionality
  intro x
  have hDspec : x ∈ D ↔ x ∈ A ∧ x ∉ B := hD x
  have hDifferenceSpec : x ∈ Difference A B ↔ x ∈ A ∧ x ∉ B := Difference.Spec
  simp only [hDspec, hDifferenceSpec]

theorem difference_unique (A B : Set) :
    ∃! D : Set, ∀ x : Set, x ∈ D ↔ x ∈ A ∧ x ∉ B := by
  refine ⟨Difference A B, ?_, ?_⟩
  · intro x
    exact Difference.Spec
  intro D hD
  exact difference_eq_difference A B D hD

infix:70 " - " => Difference


/- There is no set to which every set belongs. [Enderton, Theorem 2A] -/
theorem thm_2A_no_universal_set : ¬ ∃ (A : Set), ∀ (x : Set), x ∈ A := by
  intro h
  obtain ⟨A, hA⟩ := h
  have hB : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ A ∧ x ∉ x := by apply comprehension
  obtain ⟨B, hB⟩ := hB
  have h : B ∈ B ↔ B ∈ A ∧ B ∉ B := by apply hB B
  have hnBB : B ∉ B := by
    intro hBB
    exact (h.mp hBB).2 hBB
  have hBB : B ∈ B := h.mpr ⟨hA B, hnBB⟩
  exact hnBB hBB

theorem no_universal_set : ¬ ∃ (A : Set), ∀ (x : Set), x ∈ A :=
  thm_2A_no_universal_set

end Set
