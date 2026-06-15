import Set.Ch2.S1_Axioms
import Set.SimpAttrs

/-!
# Chapter 2, Section 2: Arbitrary Unions and Intersections

This section includes Theorem 2B style intersection existence/uniqueness and
the derived `BigIntersection` API.
-/

namespace Set

#check comprehension
#check extensionality


-- **Union Axiom** (full form) [Enderton Ch2 §2, p.24]
#check union

/-- [Enderton Ch2 §2, pp.23-24] "For any set `A`, the *union* `⋃A` of `A` is the set defined
by `⋃A = {x | x belongs to some member of A} = {x | (∃b ∈ A) x ∈ b}`." (Union Axiom, p.24:
"For any set `A`, there exists a set `B` whose elements are exactly the members of the
members of `A`": `∀x[x ∈ B ⇔ (∃b ∈ A) x ∈ b]`.) -/
noncomputable def BigUnion (A : Set) : Set := Classical.choose (union A)

/-- [Enderton Ch2 §2, p.24] "`x ∈ ⋃A ⇔ (∃b ∈ A) x ∈ b`." (Defining property of `⋃A`.) -/
@[simp] lemma BigUnion.Spec {A x : Set} :
    x ∈ BigUnion A ↔ (∃ b : Set, b ∈ A ∧ x ∈ b) :=
  (Classical.choose_spec (union A)) x
attribute [set_spec_simps] BigUnion.Spec

/-- [Enderton Ch2 §2, p.24] "Uniqueness, as always, follows from extensionality." (Uniqueness
half of well-definedness of `⋃A`.) -/
theorem bigUnion_eq_bigUnion (A U : Set)
    (hU : ∀ x : Set, x ∈ U ↔ (∃ b : Set, b ∈ A ∧ x ∈ b)) : U = BigUnion A := by
  apply extensionality
  intro x
  have hUspec : x ∈ U ↔ (∃ b : Set, b ∈ A ∧ x ∈ b) := hU x
  have hBigUnionSpec : x ∈ BigUnion A ↔ (∃ b : Set, b ∈ A ∧ x ∈ b) := BigUnion.Spec
  simp only [hUspec, hBigUnionSpec]

/-- [Enderton Ch2 §2, p.24] "For any set `A`, there exists a set `B` whose elements are
exactly the members of the members of `A`." (Existence and uniqueness of `⋃A`.) -/
theorem bigUnion_unique (A : Set) :
    ∃! U : Set, ∀ x : Set, x ∈ U ↔ (∃ b : Set, b ∈ A ∧ x ∈ b) := by
  refine ⟨BigUnion A, ?_, ?_⟩
  · intro x
    exact BigUnion.Spec
  intro U hU
  exact bigUnion_eq_bigUnion A U hU

prefix:75 "⋃" => BigUnion

/-- [Enderton Ch2 §2, p.24] "`⋃{a, b} = {x | x belongs to some member of {a, b}} = {x | x
belongs to a or to b} = a ∪ b`." (The full-union axiom recovers binary union via pairing.) -/
theorem bigUnion_pair (A B : Set) : ⋃ (Pair A B) = A ∪ B := by
  apply extensionality
  intro x
  calc
    x ∈ ⋃ (Pair A B)
      ↔ ∃ b : Set, b ∈ Pair A B ∧ x ∈ b := BigUnion.Spec
    _ ↔ ∃ b : Set, (b = A ∨ b = B) ∧ x ∈ b := by simp [Pair.Spec]
    _ ↔ x ∈ A ∨ x ∈ B := by simp []
    _ ↔ x ∈ A ∪ B := Union.Spec.symm

/-- [Enderton Ch2 §2, p.24] "An extreme case is `⋃∅ = ∅`." -/
theorem union_of_empty_set : ⋃ Empty = Empty := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (BigUnion.Spec).mp hx with ⟨b, hb, _⟩
    exact False.elim (Empty.Spec hb)
  · intro hx
    exact False.elim (Empty.Spec hx)

/-- [Enderton Ch2 §2, p.25] "we define for every nonempty set `A`, the *intersection* `⋂A`."
(Predicate capturing the textbook's "nonempty set" hypothesis.) -/
def Nonempty (A : Set) : Prop := ∃ x : Set, x ∈ A

@[simp]
theorem not_nonempty_iff_eq_empty (A : Set) : (¬ A.Nonempty) ↔ A = Set.Empty := by
  constructor
  · intro hA
    apply empty_eq_empty
    simpa only [Nonempty, not_exists] using hA
  · intro hA
    intro hNonempty
    rcases hNonempty with ⟨x, hxA⟩
    rw [hA] at hxA
    exact Empty.Spec hxA

/-- [Enderton Ch2 §2, p.25] "**Theorem 2B** For any nonempty set `A`, there exists a unique
set `B` such that for any `x`, `x ∈ B ⇔ x belongs to every member of A`." -/
theorem thm_2B_intersection (A : Set) (h : A.Nonempty) :
    ∃! (B : Set), ∀ (x : Set), x ∈ B ↔ (∀ (a : Set), a ∈ A → x ∈ a) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨B, hBspec⟩ :
      ∃ (B : Set), ∀ (x : Set),
        x ∈ B ↔ x ∈ c ∧ ∀ (a : Set), a ∈ A ∧ a ≠ c → x ∈ a :=
          comprehension (fun x => ∀ (a : Set), a ∈ A ∧ a ≠ c → x ∈ a) c
  -- existence
  have hCanonicalSpec :
      ∀ x : Set, x ∈ B ↔ (∀ (a : Set), a ∈ A → x ∈ a) := by
    intro x
    constructor
    · intro hxB
      have hxRaw : x ∈ c ∧ ∀ (a : Set), a ∈ A ∧ a ≠ c → x ∈ a := (hBspec x).mp hxB
      intro a ha
      by_cases hEq : a = c
      · simpa [hEq] using hxRaw.1
      · exact hxRaw.2 a ⟨ha, hEq⟩
    · intro hxAll
      have hxRaw : x ∈ c ∧ ∀ (a : Set), a ∈ A ∧ a ≠ c → x ∈ a := by
        refine ⟨hxAll c hc, ?_⟩
        intro a haNe
        exact hxAll a haNe.1
      exact (hBspec x).mpr hxRaw
  refine ⟨B, hCanonicalSpec, ?_⟩
  -- uniqueness
  intro B' hB'spec
  apply extensionality
  intro x
  simp only [hB'spec, hCanonicalSpec]


/-- [Enderton Ch2 §2, p.25] "**Theorem 2B** For any nonempty set `A`, there exists a unique
set `B` such that for any `x`, `x ∈ B ⇔ x belongs to every member of A`." (Alias of
`thm_2B_intersection`.) -/
theorem intersection (A : Set) (h : A.Nonempty) :
    ∃! (B : Set), ∀ (x : Set), x ∈ B ↔ (∀ (a : Set), a ∈ A → x ∈ a) :=
  thm_2B_intersection A h

/-- [Enderton Ch2 §2, p.25] "we define for every nonempty set `A`, the *intersection* `⋂A`
of `A` by the condition `x ∈ ⋂A ⇔ x belongs to every member of A`." ("This theorem permits
defining `⋂A` to be that unique set `B`.") -/
noncomputable def BigIntersection (A : Set) (hA : A.Nonempty) : Set :=
  Classical.choose (intersection A hA)

/-- [Enderton Ch2 §2, p.25] "`x ∈ ⋂A ⇔ x belongs to every member of A`." (Defining property
of `⋂A`.) -/
@[simp] lemma BigIntersection.Spec {A x : Set} (hA : A.Nonempty) :
    x ∈ BigIntersection A hA ↔ (∀ a : Set, a ∈ A → x ∈ a) := by
  rw [BigIntersection]
  exact ((Classical.choose_spec (intersection A hA)).left) x
attribute [set_spec_simps] BigIntersection.Spec

prefix:75 "⋂" => BigIntersection

lemma pair_nonempty (A B : Set) : (Pair A B).Nonempty := by
  have hA : A ∈ Pair A B := Pair.Spec.mpr (Or.inl rfl)
  exact ⟨A, hA⟩

/-- [Enderton Ch2 §2, p.25] "`⋂{a, b} = a ∩ b`." -/
theorem bigIntersection_pair (A B : Set) :
    BigIntersection (Pair A B) (pair_nonempty A B) = A ∩ B := by
  apply extensionality
  intro x
  constructor
  · intro hx
    simp only [Intersection.Spec]
    simp [BigIntersection.Spec (pair_nonempty A B), Pair.Spec] at hx
    exact hx
  · intro hx
    simp only [Intersection.Spec] at hx
    simp [BigIntersection.Spec (pair_nonempty A B), Pair.Spec]
    exact hx



/-- [Enderton Ch2 §2, p.26] "If `b ∈ A`, then `b ⊆ ⋃A`." -/
theorem member_subset_bigUnion (A b : Set) (hb : b ∈ A) : b ⊆ ⋃ A := by
  intro x hx
  simp [BigUnion.Spec]
  exact ⟨b, hb, hx⟩


end Set
