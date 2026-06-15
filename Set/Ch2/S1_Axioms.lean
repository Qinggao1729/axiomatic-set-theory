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

-- **Extensionality Axiom** [Enderton Ch2 §1, p.17]
#check extensionality


-- **Empty Set Axiom** [Enderton Ch2 §1, p.18]
#check empty

/-- [Enderton Ch2 §1, p.18] "**Definition** `∅` is the set having no members."
(Empty Set Axiom, p.18: "There is a set having no members", `∃B ∀x x ∉ B`.) -/
noncomputable def Empty : Set := Classical.choose empty

/-- [Enderton Ch2 §1, p.18] "`∅` is the set having no members." (Defining property of `∅`.) -/
@[simp] lemma Empty.Spec {x : Set} : x ∉ Empty :=
  (Classical.choose_spec empty) x
attribute [set_spec_simps] Empty.Spec

/-- [Enderton Ch2 §1, p.18] "we must know that there cannot be more than one set having
no members. ... extensionality provides the second." (Uniqueness half of the
well-definedness of `∅`: any memberless set equals `∅`.) -/
theorem empty_eq_empty (A : Set) (hA : ∀ x : Set, x ∉ A) : A = Empty := by
  apply extensionality
  intro x
  constructor
  · intro hx
    exact False.elim (hA x hx)
  · intro hx
    exact False.elim (Empty.Spec hx)

/-- [Enderton Ch2 §1, p.18] "We must know that there exists a set having no members, and
we must know that there cannot be more than one set having no members." (Existence and
uniqueness of `∅`.) -/
theorem empty_unique : ∃! B : Set, ∀ x : Set, x ∉ B := by
  refine ⟨Empty, ?_, ?_⟩
  · intro x
    exact Empty.Spec
  intro B hB
  exact empty_eq_empty B hB

notation "∅" => Empty


-- **Pairing Axiom** [Enderton Ch2 §1, p.18]
#check pairing

/-- [Enderton Ch2 §1, p.19] "**Definition** (i) For any sets `u` and `v`, the *pair set*
`{u, v}` is the set whose only members are `u` and `v`." (Pairing Axiom, p.18:
`∀u ∀v ∃B ∀x(x ∈ B ⇔ x = u or x = v)`.) -/
noncomputable def Pair (u v : Set) : Set := Classical.choose (pairing u v)
notation:max "{" x ", " y "}" => Pair x y

/-- [Enderton Ch2 §1, p.19] "the *pair set* `{u, v}` is the set whose only members are `u`
and `v`." (Defining property of `{u, v}`.) -/
@[simp] lemma Pair.Spec {u v x : Set} : x ∈ Pair u v ↔ x = u ∨ x = v :=
  (Classical.choose_spec (pairing u v)) x
attribute [set_spec_simps] Pair.Spec

/-- [Enderton Ch2 §1, p.19] "extensionality assures us that the sets being named are
unique." (Uniqueness half of well-definedness of `{u, v}`.) -/
theorem pair_eq_pair (u v A : Set)
    (hA : ∀ x : Set, x ∈ A ↔ x = u ∨ x = v) : A = Pair u v := by
  apply extensionality
  intro x
  have hAspec : x ∈ A ↔ x = u ∨ x = v := hA x
  have hPspec : x ∈ Pair u v ↔ x = u ∨ x = v := Pair.Spec
  simp only [hAspec, hPspec]

/-- [Enderton Ch2 §1, p.19] "our set existence axioms assure us that the sets being named
exist, and extensionality assures us that the sets being named are unique." (Existence and
uniqueness of `{u, v}`.) -/
theorem pair_unique (u v : Set) :
    ∃! B : Set, ∀ x : Set, x ∈ B ↔ x = u ∨ x = v := by
  refine ⟨Pair u v, ?_, ?_⟩
  · intro x
    exact Pair.Spec
  intro B hB
  exact pair_eq_pair u v B hB


/-- [Enderton Ch2 §1, p.19] "given any `x` we have the *singleton* `{x}`, which is defined
to be `{x, x}`." -/
noncomputable def Singleton (x : Set) : Set := Classical.choose (pairing x x)
notation:max "{" x "}" => Singleton x

/-- [Enderton Ch2 §1, p.19] "the *singleton* `{x}`, which is defined to be `{x, x}`."
(Defining property of `{x}`.) -/
@[simp] lemma Singleton.Spec {x y : Set} : y ∈ Singleton x ↔ y = x := by
  have hSingletonSpec : y ∈ Singleton x ↔ y = x ∨ y = x :=
    Classical.choose_spec (pairing x x) y
  simp only [hSingletonSpec, or_self]
attribute [set_spec_simps] Singleton.Spec


-- **Power Set Axiom** [Enderton Ch2 §1, p.18]
#check power

/-- [Enderton Ch2 §1, p.19] "**Definition** (iii) For any set `a`, the *power set* `𝒫a` is
the set whose members are exactly the subsets of `a`." (Power Set Axiom, p.18:
`∀a ∃B ∀x(x ∈ B ⇔ x ⊆ a)`.) -/
noncomputable def Power (A : Set) : Set := Classical.choose (power A)

/-- [Enderton Ch2 §1, p.19] "the *power set* `𝒫a` is the set whose members are exactly the
subsets of `a`." (Defining property of `𝒫A`.) -/
@[simp] lemma Power.Spec {A x : Set} : x ∈ Power A ↔ x ⊆ A :=
  (Classical.choose_spec (power A)) x
attribute [set_spec_simps] Power.Spec

/-- [Enderton Ch2 §1, p.19] "extensionality assures us that the sets being named are
unique." (Uniqueness half of well-definedness of `𝒫A`.) -/
theorem power_eq_power (A B : Set)
    (hB : ∀ x : Set, x ∈ B ↔ x ⊆ A) : B = Power A := by
  apply extensionality
  intro x
  have hBspec : x ∈ B ↔ x ⊆ A := hB x
  have hPspec : x ∈ Power A ↔ x ⊆ A := Power.Spec
  simp only [hBspec, hPspec]

/-- [Enderton Ch2 §1, p.19] "our set existence axioms assure us that the sets being named
exist, and extensionality assures us that the sets being named are unique." (Existence and
uniqueness of `𝒫A`.) -/
theorem power_unique (A : Set) :
    ∃! B : Set, ∀ x : Set, x ∈ B ↔ x ⊆ A := by
  refine ⟨Power A, ?_, ?_⟩
  · intro x
    exact Power.Spec
  intro B hB
  exact power_eq_power A B hB

prefix:75 "𝒫" => Power


-- **Union Axiom, Preliminary Form** [Enderton Ch2 §1, p.18]
#check union_preliminary

/-- [Enderton Ch2 §1, p.19] "**Definition** (ii) For any sets `a` and `b`, the *union*
`a ∪ b` is the set whose members are those sets belonging either to `a` or to `b` (or
both)." (Union Axiom, Preliminary Form, p.18:
`∀a ∀b ∃B ∀x(x ∈ B ⇔ x ∈ a or x ∈ b)`.) -/
noncomputable def Union (A B : Set) : Set := Classical.choose (union_preliminary A B)

/-- [Enderton Ch2 §1, p.19] "the *union* `a ∪ b` is the set whose members are those sets
belonging either to `a` or to `b` (or both)." (Defining property of `a ∪ b`.) -/
@[simp] lemma Union.Spec {A B x : Set} : x ∈ Union A B ↔ x ∈ A ∨ x ∈ B :=
  (Classical.choose_spec (union_preliminary A B)) x
attribute [set_spec_simps] Union.Spec

/-- [Enderton Ch2 §1, p.19] "extensionality assures us that the sets being named are
unique." (Uniqueness half of well-definedness of `a ∪ b`.) -/
theorem union_eq_union (A B U : Set)
    (hU : ∀ x : Set, x ∈ U ↔ x ∈ A ∨ x ∈ B) : U = Union A B := by
  apply extensionality
  intro x
  have hUspec : x ∈ U ↔ x ∈ A ∨ x ∈ B := hU x
  have hUnionSpec : x ∈ Union A B ↔ x ∈ A ∨ x ∈ B := Union.Spec
  simp only [hUspec, hUnionSpec]

/-- [Enderton Ch2 §1, p.19] "our set existence axioms assure us that the sets being named
exist, and extensionality assures us that the sets being named are unique." (Existence and
uniqueness of `a ∪ b`.) -/
theorem union_unique (A B : Set) :
    ∃! U : Set, ∀ x : Set, x ∈ U ↔ x ∈ A ∨ x ∈ B := by
  refine ⟨Union A B, ?_, ?_⟩
  · intro x
    exact Union.Spec
  intro U hU
  exact union_eq_union A B U hU

infix:70 " ∪ " => Union


-- **Subset Axioms / comprehension schema** [Enderton Ch2 §1, p.21]
#check comprehension

/-- [Enderton Ch2 §1, p.21] "**Subset Axioms** For each formula `__` not containing `B`,
the following is an axiom: `∀t₁ ⋯ ∀tₖ ∀c ∃B ∀x(x ∈ B ⇔ x ∈ c & __)`." (The set `B` "can be
named by use of a variation on the abstraction notation: `B = {x ∈ c | __}`".) -/
noncomputable def Comprehension (P : Set → Prop) (c : Set) : Set :=
  Classical.choose (comprehension P c)

/-- [Enderton Ch2 §1, p.21] "a set `B` whose members are exactly those sets `x` in `c` such
that `__`." (Defining property of `{x ∈ c | P x}`.) -/
@[simp] lemma Comprehension.Spec {P : Set → Prop} {c x : Set} :
    x ∈ Comprehension P c ↔ x ∈ c ∧ P x := by
  rw [Comprehension]
  exact (Classical.choose_spec (comprehension P c)) x
attribute [set_spec_simps] Comprehension.Spec

/-- [Enderton Ch2 §1, p.21] "The set `B` is uniquely determined (by `t₁, …, tₖ` and `c`)."
(Uniqueness half of well-definedness of `{x ∈ c | P x}`.) -/
theorem comprehension_eq_comprehension (P : Set → Prop) (c C : Set)
    (hC : ∀ x : Set, x ∈ C ↔ x ∈ c ∧ P x) : C = Comprehension P c := by
  apply extensionality
  intro x
  have hCspec : x ∈ C ↔ x ∈ c ∧ P x := hC x
  have hComprehensionSpec : x ∈ Comprehension P c ↔ x ∈ c ∧ P x := Comprehension.Spec
  simp only [hCspec, hComprehensionSpec]

/-- [Enderton Ch2 §1, p.21] "In English, the axiom asserts ... the existence of a set `B`
whose members are exactly those sets `x` in `c` such that `__`. ... The set `B` is uniquely
determined." (Existence and uniqueness of `{x ∈ c | P x}`.) -/
theorem comprehension_unique (P : Set → Prop) (c : Set) :
    ∃! C : Set, ∀ x : Set, x ∈ C ↔ x ∈ c ∧ P x := by
  refine ⟨Comprehension P c, ?_, ?_⟩
  · intro x
    exact Comprehension.Spec
  intro C hC
  exact comprehension_eq_comprehension P c C hC


/-- [Enderton Ch2 §1, p.21] "One of the subset axioms is: `∀a ∀c ∃B ∀x(x ∈ B ⇔ x ∈ c & x ∈
a)`. This axiom asserts the existence of the set we define to be the *intersection* `c ∩ a`
of `c` and `a`." -/
noncomputable def Intersection (A B : Set) : Set :=
  Comprehension (fun x => x ∈ B) A

/-- [Enderton Ch2 §1, p.21] "the *intersection* `c ∩ a` of `c` and `a`." (Defining property
of `A ∩ B`.) -/
@[simp] lemma Intersection.Spec {A B x : Set} : x ∈ Intersection A B ↔ x ∈ A ∧ x ∈ B := by
  simp [Intersection, Comprehension.Spec]
attribute [set_spec_simps] Intersection.Spec

/-- [Enderton Ch2 §1, p.21] "The set `B` is uniquely determined." (Uniqueness half of
well-definedness of `A ∩ B`.) -/
theorem intersection_eq_intersection (A B I : Set)
    (hI : ∀ x : Set, x ∈ I ↔ x ∈ A ∧ x ∈ B) : I = Intersection A B := by
  apply extensionality
  intro x
  have hIspec : x ∈ I ↔ x ∈ A ∧ x ∈ B := hI x
  have hIntersectionSpec : x ∈ Intersection A B ↔ x ∈ A ∧ x ∈ B := Intersection.Spec
  simp only [hIspec, hIntersectionSpec]

/-- [Enderton Ch2 §1, p.21] "This axiom asserts the existence of the set we define to be the
*intersection* `c ∩ a`." (Existence and uniqueness of `A ∩ B`.) -/
theorem intersection_unique (A B : Set) :
    ∃! I : Set, ∀ x : Set, x ∈ I ↔ x ∈ A ∧ x ∈ B := by
  refine ⟨Intersection A B, ?_, ?_⟩
  · intro x
    exact Intersection.Spec
  intro I hI
  exact intersection_eq_intersection A B I hI

infix:70 " ∩ " => Intersection


/-- [Enderton Ch2 §1, p.21] "we will also allow as a subset axiom: `∀A ∀B ∃S ∀t[t ∈ S ⇔ t ∈
A & t ∉ B]`. This set `S` is the *relative complement* of `B` in `A`, denoted `A − B`." -/
noncomputable def Difference (A B : Set) : Set :=
  Comprehension (fun x => x ∉ B) A

/-- [Enderton Ch2 §1, p.21] "the *relative complement* of `B` in `A`, denoted `A − B`."
(Defining property of `A - B`.) -/
@[simp] lemma Difference.Spec {A B x : Set} : x ∈ Difference A B ↔ x ∈ A ∧ x ∉ B := by
  simp [Difference, Comprehension.Spec]
attribute [set_spec_simps] Difference.Spec

/-- [Enderton Ch2 §1, p.21] "The set `B` is uniquely determined." (Uniqueness half of
well-definedness of `A - B`.) -/
theorem difference_eq_difference (A B D : Set)
    (hD : ∀ x : Set, x ∈ D ↔ x ∈ A ∧ x ∉ B) : D = Difference A B := by
  apply extensionality
  intro x
  have hDspec : x ∈ D ↔ x ∈ A ∧ x ∉ B := hD x
  have hDifferenceSpec : x ∈ Difference A B ↔ x ∈ A ∧ x ∉ B := Difference.Spec
  simp only [hDspec, hDifferenceSpec]

/-- [Enderton Ch2 §1, p.21] "This set `S` is the *relative complement* of `B` in `A`, denoted
`A − B`." (Existence and uniqueness of `A - B`.) -/
theorem difference_unique (A B : Set) :
    ∃! D : Set, ∀ x : Set, x ∈ D ↔ x ∈ A ∧ x ∉ B := by
  refine ⟨Difference A B, ?_, ?_⟩
  · intro x
    exact Difference.Spec
  intro D hD
  exact difference_eq_difference A B D hD

infix:70 " - " => Difference


/-- [Enderton Ch2 §1, p.22] "**Theorem 2A** There is no set to which every set belongs." -/
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
