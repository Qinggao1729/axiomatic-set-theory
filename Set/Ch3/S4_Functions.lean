import Set.Ch3.S2_Relations
import Set.Ch2.S2_ArbitraryUnionsIntersections
import Set.SimpAttrs

/-!
# Chapter 3, Section 4: Functions

Function definitions and theorems (3E/3F/3G/3H/3I/3K/3L-style results).
-/

namespace Set
  -- Function [Enderton, p.42]
  def IsFunction (F : Set) : Prop :=
    IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟨x, y⟩ ∈ F
  def MapsInto (F A B : Set) : Prop :=
    IsFunction F ∧ (dom F) = A ∧ SubsetOf (ran F) B
  def MapsOnto (F A B : Set) : Prop :=
    MapsInto F A B ∧ (ran F) = B
  -- A set R is single-rooted iff for each y ∈ ran R there is only one x such that xRy.
  def IsSingleRooted (R : Set) : Prop :=
    ∀ (y : Set), y ∈ (ran R) → ∃! (x: Set), ⟨x, y⟩ ∈ R
  def IsOneToOne (F : Set) : Prop := IsFunction F ∧ IsSingleRooted F

  lemma MapsInto.dom_mem_iff (F A B x : Set) :
      MapsInto F A B → (x ∈ (dom F) ↔ x ∈ A) := by
    intro hMap
    rcases hMap with ⟨_, hDomEq, _⟩
    simp [hDomEq]

  noncomputable def Identity (A : Set) : Set :=
    Comprehension (λ w ↦ ∃ x, x ∈ A ∧ w = ⟨x, x⟩) (A ⨯ A)

  lemma Identity.Spec {A w : Set} : w ∈ Identity A ↔ w ∈ (A ⨯ A) ∧ ∃ x, x ∈ A ∧ w = ⟨x, x⟩ := by
    simp [Identity, Comprehension.Spec]
  attribute [set_spec_simps] Identity.Spec

  lemma Identity.Pair.Spec {A x y : Set} :
      ⟨x, y⟩ ∈ Identity A ↔ x ∈ A ∧ y = x := by
    constructor
    · intro hxy
      rcases (Identity.Spec).1 hxy with ⟨_, hEx⟩
      rcases hEx with ⟨u, huA, hEq⟩
      rcases (OrderedPair.uniqueness x y u u).1 hEq with ⟨hxu, hyu⟩
      subst hxu
      exact ⟨huA, hyu⟩
    · intro hxy
      rcases hxy with ⟨hxA, hyx⟩
      have hProd : ⟨x, x⟩ ∈ (A ⨯ A) := by
        rw [Product.Spec_full]
        refine ⟨?_, ?_⟩
        · exact OrderedPair.in_power_power x x (A ∪ A)
            ((Union.Spec).2 (Or.inl hxA))
            ((Union.Spec).2 (Or.inr hxA))
        · exact ⟨x, x, hxA, hxA, rfl⟩
      have hxx : ⟨x, x⟩ ∈ Identity A := by
        exact (Identity.Spec).2
          (And.intro hProd (Exists.intro x (And.intro hxA rfl)))
      simpa [hyx] using hxx
  attribute [set_spec_simps] Identity.Pair.Spec

  /-
  Function operations [Enderton, p. 44]
  -/
  -- Arbitrary sets
  noncomputable def Inverse (F : Set) :=
    Comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ w = ⟨v, u⟩) ((ran F) ⨯ (dom F))
  @[simp]
  lemma Inverse.Spec {F x : Set} : x ∈ Inverse F ↔ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ x = ⟨v, u⟩ := by
    rw [Inverse, Comprehension.Spec]
    constructor
    · intro hx
      exact hx.2
    · intro hx
      rcases hx with ⟨u, v, huvF, hxEq⟩
      have hvRan : v ∈ ran F := (Relation.Range.Spec).2 ⟨u, huvF⟩
      have huDom : u ∈ dom F := (Relation.Domain.Spec).2 ⟨v, huvF⟩
      have hxProd : x ∈ (ran F) ⨯ (dom F) := by
        subst hxEq
        apply (Product.Spec_full (ran F) (dom F) (OrderedPair v u)).2
        refine ⟨?_, ?_⟩
        · exact OrderedPair.in_power_power v u ((ran F) ∪ (dom F))
            ((Union.Spec).2 (Or.inl hvRan))
            ((Union.Spec).2 (Or.inr huDom))
        · exact ⟨v, u, hvRan, huDom, rfl⟩
      exact ⟨hxProd, ⟨u, v, huvF, hxEq⟩⟩
  attribute [set_spec_simps] Inverse.Spec
  postfix:90 "⁻¹" => Inverse
  noncomputable def Composition (F G : Set) :=
    Comprehension
      (λ w ↦ ∃ (u v t : Set), ⟨u, t⟩ ∈ G ∧ ⟨t, v⟩ ∈ F ∧ w = ⟨u, v⟩)
      ((dom G) ⨯ (ran F))
  @[simp]
  lemma Composition.Spec {F G x : Set} : x ∈ Composition F G ↔ (x ∈ ((dom G) ⨯ (ran F))) ∧ ∃ (u v t : Set), ⟨u, t⟩ ∈ G ∧ ⟨t, v⟩ ∈ F ∧ x = ⟨u, v⟩ := by
    simp [Composition, Comprehension.Spec]
  attribute [set_spec_simps] Composition.Spec
  infixr:90 " ∘ " => Composition
  noncomputable def Restriction (F : Set) (C : Set) :=
    Comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ u ∈ C ∧ w = ⟨u, v⟩) F
  @[simp]
  lemma Restriction.Spec {F C w : Set} : w ∈ Restriction F C ↔ w ∈ F ∧ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ u ∈ C ∧ w = ⟨u, v⟩ := by
    simp [Restriction, Comprehension.Spec]
  attribute [set_spec_simps] Restriction.Spec
  @[simp]
  lemma Restriction.Pair.Spec {F C u v : Set} : ⟨u, v⟩ ∈ Restriction F C ↔ ⟨u, v⟩ ∈ F ∧ u ∈ C := by
    rw [Restriction.Spec]
    constructor
    · intro h
      rcases h with ⟨hF, x, y, hxy, hxC, hEq⟩
      rcases (OrderedPair.uniqueness u v x y).1 hEq with ⟨hux, hvy⟩
      subst hux hvy
      exact ⟨hxy, hxC⟩
    · intro h
      rcases h with ⟨hF, hC⟩
      exact ⟨hF, u, v, hF, hC, rfl⟩
  attribute [set_spec_simps] Restriction.Pair.Spec
  infixr:90 " ↾ " => Restriction
  noncomputable def Image (F : Set) (C : Set) :=
    ran (Restriction F C)
  notation:90 F "⟦" A "⟧" => Image F A
  @[simp]
  lemma Image.Spec {F C y : Set} : y ∈ F⟦C⟧ ↔ ∃ u, u ∈ C ∧ ⟨u, y⟩ ∈ F := by
    rw [Image, Relation.Range.Spec]
    constructor
    · intro h
      rcases h with ⟨u, hu⟩
      rw [Restriction.Pair.Spec] at hu
      exact ⟨u, hu.right, hu.left⟩
    · intro h
      rcases h with ⟨u, huC, huF⟩
      exact ⟨u, (Restriction.Pair.Spec).2 ⟨huF, huC⟩⟩
  attribute [set_spec_simps] Image.Spec

  lemma Pair.mem_dom (F x y : Set) : ⟨x, y⟩ ∈ F → x ∈ dom F := by
    intro h
    exact (Relation.Domain.Spec).2 ⟨y, h⟩

  lemma Pair.mem_ran (F x y : Set) : ⟨x, y⟩ ∈ F → y ∈ ran F := by
    intro h
    exact (Relation.Range.Spec).2 ⟨x, h⟩

  lemma Pair.mem_product (A B x y : Set) : x ∈ A → y ∈ B → ⟨x, y⟩ ∈ A ⨯ B := by
    intro hx hy
    rw [Product.Spec_full]
    refine And.intro ?_ ?_
    · exact OrderedPair.in_power_power x y (A ∪ B)
        ((Union.Spec).2 (Or.inl hx))
        ((Union.Spec).2 (Or.inr hy))
    · exact ⟨x, y, hx, hy, rfl⟩

  lemma Pair.mem_product_elim (A B x y : Set) :
      ⟨x, y⟩ ∈ A ⨯ B → x ∈ A ∧ y ∈ B := by
    intro hxy
    rcases (Product.Spec).1 hxy with ⟨u, v, huA, hvB, hEq⟩
    rcases (OrderedPair.uniqueness x y u v).1 hEq with ⟨hxu, hyv⟩
    subst hxu hyv
    exact ⟨huA, hvB⟩

  lemma function_value_unique (F x y z : Set) (hF : IsFunction F) :
      ⟨x, y⟩ ∈ F → ⟨x, z⟩ ∈ F → y = z := by
    intro hxy hxz
    rcases hF with ⟨_, huniq⟩
    have hxdom : x ∈ dom F := Pair.mem_dom F x y hxy
    rcases huniq x hxdom with ⟨w, hw, hwuniq⟩
    have hyw : y = w := hwuniq y hxy
    have hzw : z = w := hwuniq z hxz
    exact hyw.trans hzw.symm

  @[simp]
  lemma Inverse.Pair.Spec {F x y : Set} : ⟨x, y⟩ ∈ Inverse F ↔ ⟨y, x⟩ ∈ F := by
    rw [Inverse.Spec]
    constructor
    · intro h
      rcases h with ⟨u, v, huv, hEq⟩
      rcases (OrderedPair.uniqueness x y v u).1 hEq with ⟨hxv, hyu⟩
      subst hxv hyu
      exact huv
    · intro h
      exact ⟨y, x, h, rfl⟩
  attribute [set_spec_simps] Inverse.Pair.Spec

  @[simp]
  lemma Composition.Pair.Spec {F G x y : Set} :
      ⟨x, y⟩ ∈ Composition F G ↔ ∃ t, ⟨x, t⟩ ∈ G ∧ ⟨t, y⟩ ∈ F := by
    rw [Composition.Spec]
    constructor
    · intro h
      rcases h with ⟨_, u, v, t, hu, hv, hEq⟩
      rcases (OrderedPair.uniqueness x y u v).1 hEq with ⟨hxu, hyv⟩
      subst hxu hyv
      exact ⟨t, hu, hv⟩
    · intro h
      rcases h with ⟨t, hxt, hty⟩
      refine And.intro ?_ ?_
      · exact Pair.mem_product (dom G) (ran F) x y (Pair.mem_dom G x t hxt) (Pair.mem_ran F t y hty)
      · exact ⟨x, y, t, hxt, hty, rfl⟩
  attribute [set_spec_simps] Composition.Pair.Spec

  /-
  [Enderton, Theorem 3E, p. 46]
  For a set F, dom F⁻¹ = ran F and ran F⁻¹ = dom F. For a relation F, (F⁻¹)⁻¹ = F.
  -/
  theorem domain_inverse (F : Set) : (dom (Inverse F)) = ran F := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro h
      rw [Relation.Domain.Spec] at h
      obtain ⟨y, hy⟩ := h
      rw [Inverse.Spec] at hy
      obtain ⟨u, v, huv⟩ := hy
      rcases huv with ⟨huvF, hEq⟩
      rcases (OrderedPair.uniqueness x y v u).1 hEq with ⟨hxv, _⟩
      subst hxv
      exact (Relation.Range.Spec).2 ⟨u, huvF⟩
    }
    { intro h
      rcases (Relation.Range.Spec).1 h with ⟨y, hyx⟩
      exact (Relation.Domain.Spec).2 ⟨y, (Inverse.Pair.Spec).2 hyx⟩
    }
  theorem range_inverse (F : Set) : (ran (Inverse F)) = dom F := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro h
      rw [Relation.Range.Spec] at h
      obtain ⟨y, hy⟩ := h
      have hxy : ⟨x, y⟩ ∈ F := (Inverse.Pair.Spec).1 hy
      exact (Relation.Domain.Spec).2 ⟨y, hxy⟩
    }
    { intro h
      rcases (Relation.Domain.Spec).1 h with ⟨y, hxy⟩
      exact (Relation.Range.Spec).2 ⟨y, (Inverse.Pair.Spec).2 hxy⟩
    }
  theorem relation_inverse_inverse (F : Set) {hF : IsRelation F} : (Inverse (Inverse F)) = F := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro hx
      rw [Inverse.Spec] at hx
      obtain ⟨u, v, ⟨huv, huvx⟩⟩ := hx
      rw [Inverse.Spec] at huv
      obtain ⟨u', v', ⟨huv', huvx'⟩⟩ := huv
      subst huvx
      have heq : u = v' ∧ v = u' := by
        rw [OrderedPair.uniqueness] at huvx'
        exact huvx'
      rw [heq.left, heq.right]
      exact huv'
    }
    { intro hx
      rcases hF x hx with ⟨u, v, rfl⟩
      have hvu : ⟨v, u⟩ ∈ Inverse F := (Inverse.Pair.Spec).2 hx
      exact (Inverse.Pair.Spec).2 hvu
    }


  /-
  [Enderton, Theorem 3F, p. 46]
  For a set F, F⁻¹ is a function iff F is single-rooted. A relation F is a function iff F⁻¹ is single-rooted.
  -/
  theorem inverse_single_rooted (F : Set) : IsFunction (Inverse F) ↔ IsSingleRooted F := by
    apply Iff.intro
    { intro hFi
      rw [IsFunction, domain_inverse] at hFi
      obtain ⟨_, hFi⟩ := hFi
      rw [IsSingleRooted]
      intro x hx
      obtain ⟨y, hxyInv, huniq⟩ := hFi x hx
      refine ⟨y, (Inverse.Pair.Spec).1 hxyInv, ?_⟩
      intro y' hy'xF
      have hxy'Inv : ⟨x, y'⟩ ∈ Inverse F := (Inverse.Pair.Spec).2 hy'xF
      exact huniq y' hxy'Inv
    }
    {
      -- IsSingleRooted F → F⁻¹ is a function
      intro h
      rw [IsSingleRooted] at h
      apply And.intro
      { -- Show: F⁻¹ is a relation
        rw [IsRelation]
        intro w hw
        rcases (Inverse.Spec).1 hw with ⟨u, v, _, hEq⟩
        exact ⟨v, u, hEq⟩
      }
      {
        intro x hx
        rw [domain_inverse] at hx
        obtain ⟨y, hyxF, hyuniq⟩ := h x hx
        refine ⟨y, (Inverse.Pair.Spec).2 hyxF, ?_⟩
        intro y' hy'
        have hy'xF : ⟨y', x⟩ ∈ F := (Inverse.Pair.Spec).1 hy'
        exact hyuniq y' hy'xF
      }
    }
  theorem relation_function_single_rooted (F : Set) {hR : IsRelation F} : IsFunction F ↔ IsSingleRooted (Inverse F) := by
    have hInv : IsFunction (Inverse (Inverse F)) ↔ IsSingleRooted (Inverse F) :=
      inverse_single_rooted (Inverse F)
    simpa [relation_inverse_inverse (F := F) (hF := hR)] using hInv

  /-
  [Enderton, Theorem 3G, p. 46]
  Assume that F is a one-to-one function. If x ∈ dom F, then F⁻¹(F(x)) = x. If y ∈ ran F, then F(F⁻¹(y)) = y.
  -/
  theorem one_to_one_inverse (F : Set) : IsFunction F ∧ IsSingleRooted F → (∀ x, x ∈ (dom F) → ∃ y, ⟨x, y⟩ ∈ F ∧ ⟨y, x⟩ ∈ F⁻¹) := by
    intro hOne
    rcases hOne with ⟨hF, _⟩
    intro x hx
    rcases hF with ⟨_, huniq⟩
    rcases huniq x hx with ⟨y, hxy, _⟩
    exact ⟨y, hxy, (Inverse.Pair.Spec).2 hxy⟩
  theorem one_to_one_inverse' (F : Set) : IsFunction F ∧ IsSingleRooted F → (∀ y, y ∈ (ran F) → ∃ x, ⟨y, x⟩ ∈ F⁻¹ ∧ ⟨x, y⟩ ∈ F) := by
    intro _
    intro y hy
    rcases (Relation.Range.Spec).1 hy with ⟨x, hxy⟩
    exact ⟨x, (Inverse.Pair.Spec).2 hxy, hxy⟩

  /-
  [Enderton, Theorem 3H, p. 47]
  If F and G are functions, then F ∘ G is a function.
  -/
  theorem composition_is_function (F G : Set) : IsFunction F → IsFunction G → IsFunction (Composition F G) := by
    intro hF hG
    refine And.intro ?_ ?_
    · intro w hw
      rw [Composition.Spec] at hw
      rcases hw with ⟨_, u, v, _, _, _, hEq⟩
      exact ⟨u, v, hEq⟩
    · intro x hx
      rw [Relation.Domain.Spec] at hx
      rcases hx with ⟨y, hxy⟩
      rcases (Composition.Pair.Spec).1 hxy with ⟨t, hxt, hty⟩
      refine ⟨y, hxy, ?_⟩
      intro y' hxy'
      rcases (Composition.Pair.Spec).1 hxy' with ⟨t', hxt', ht'y'⟩
      have htt' : t = t' := function_value_unique G x t t' hG hxt hxt'
      subst htt'
      exact (function_value_unique F t y y' hF hty ht'y').symm

  noncomputable def CompositionDomain (F G : Set) : Set :=
    Comprehension (λ x ↦ ∃ t, ⟨x, t⟩ ∈ G ∧ t ∈ (dom F)) (dom G)

  lemma CompositionDomain.Spec {F G x : Set} :
      x ∈ CompositionDomain F G ↔ x ∈ (dom G) ∧ ∃ t, ⟨x, t⟩ ∈ G ∧ t ∈ (dom F) := by
    simp [CompositionDomain, Comprehension.Spec]

  theorem composition_domain (F G : Set) :
      Relation.Domain (Composition F G) = CompositionDomain F G := by
    apply extensionality
    intro x
    apply Iff.intro
    · intro hx
      rw [Relation.Domain.Spec] at hx
      rcases hx with ⟨y, hxy⟩
      rcases (Composition.Pair.Spec).1 hxy with ⟨t, hxt, hty⟩
      rw [CompositionDomain.Spec]
      exact ⟨Pair.mem_dom G x t hxt, t, hxt, Pair.mem_dom F t y hty⟩
    · intro hx
      rw [CompositionDomain.Spec] at hx
      rcases hx with ⟨_, t, hxt, htDomF⟩
      rw [Relation.Domain.Spec] at htDomF
      rcases htDomF with ⟨y, hty⟩
      rw [Relation.Domain.Spec]
      exact ⟨y, (Composition.Pair.Spec).2 ⟨t, hxt, hty⟩⟩

  /-
  [Enderton, Theorem 3I / 3I in our todo numbering]
  (F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹
  -/
  theorem inverse_composition (F G : Set) : (Composition F G)⁻¹ = Composition (Inverse G) (Inverse F) := by
    apply extensionality
    intro w
    apply Iff.intro
    · intro hw
      rw [Inverse.Spec] at hw
      rcases hw with ⟨u, v, huv, rfl⟩
      rcases (Composition.Pair.Spec).1 huv with ⟨t, hut, htv⟩
      exact (Composition.Pair.Spec).2
        ⟨t, (Inverse.Pair.Spec).2 htv, (Inverse.Pair.Spec).2 hut⟩
    · intro hw
      rw [Composition.Spec] at hw
      rcases hw with ⟨_, u, v, t, hut, htv, rfl⟩
      rw [Inverse.Pair.Spec] at hut htv
      exact (Inverse.Pair.Spec).2
        ((Composition.Pair.Spec).2 ⟨t, htv, hut⟩)

  theorem image_union (F A B : Set) : F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧ := by
    apply extensionality
    intro y
    constructor
    · intro h
      rcases (Image.Spec).1 h with ⟨x, hxAB, hxy⟩
      rcases (Union.Spec).1 hxAB with hxA | hxB
      · exact (Union.Spec).2 (Or.inl ((Image.Spec).2 ⟨x, hxA, hxy⟩))
      · exact (Union.Spec).2 (Or.inr ((Image.Spec).2 ⟨x, hxB, hxy⟩))
    · intro h
      rcases (Union.Spec).1 h with hA | hB
      · rcases (Image.Spec).1 hA with ⟨x, hxA, hxy⟩
        exact (Image.Spec).2 ⟨x, (Union.Spec).2 (Or.inl hxA), hxy⟩
      · rcases (Image.Spec).1 hB with ⟨x, hxB, hxy⟩
        exact (Image.Spec).2 ⟨x, (Union.Spec).2 (Or.inr hxB), hxy⟩

  theorem image_inter_subset (F A B : Set) : F⟦A ∩ B⟧ ⊆ F⟦A⟧ ∩ F⟦B⟧ := by
    intro y hy
    rw [Image.Spec] at hy
    rcases hy with ⟨x, hxAB, hxy⟩
    rw [Intersection.Spec] at hxAB
    rw [Intersection.Spec, Image.Spec, Image.Spec]
    exact ⟨⟨x, hxAB.left, hxy⟩, ⟨x, hxAB.right, hxy⟩⟩

  theorem image_diff_subset (F A B : Set) : F⟦A⟧ - F⟦B⟧ ⊆ F⟦A - B⟧ := by
    intro y hy
    rw [Difference.Spec, Image.Spec] at hy
    rcases hy with ⟨⟨x, hxA, hxy⟩, hyNotB⟩
    have hxNotB : x ∉ B := by
      intro hxB
      apply hyNotB
      exact (Image.Spec).2 ⟨x, hxB, hxy⟩
    exact (Image.Spec).2 ⟨x, (Difference.Spec).2 ⟨hxA, hxNotB⟩, hxy⟩

  theorem inverse_image_union (G A B : Set) :
      (G⁻¹)⟦A ∪ B⟧ = (G⁻¹)⟦A⟧ ∪ (G⁻¹)⟦B⟧ := by
    simpa using image_union (G⁻¹) A B

  theorem inverse_image_inter (G A B : Set) (hG : IsFunction G) :
      (G⁻¹)⟦A ∩ B⟧ = (G⁻¹)⟦A⟧ ∩ (G⁻¹)⟦B⟧ := by
    apply extensionality
    intro y
    constructor
    · intro h
      rcases (Image.Spec).1 h with ⟨x, hxAB, hyxInv⟩
      rcases (Intersection.Spec).1 hxAB with ⟨hxA, hxB⟩
      refine (Intersection.Spec).2 ?_
      refine ⟨?_, ?_⟩
      · exact (Image.Spec).2 ⟨x, hxA, hyxInv⟩
      · exact (Image.Spec).2 ⟨x, hxB, hyxInv⟩
    · intro h
      rcases (Intersection.Spec).1 h with ⟨hyA, hyB⟩
      rcases (Image.Spec).1 hyA with ⟨x₁, hx₁A, hyx₁Inv⟩
      rcases (Image.Spec).1 hyB with ⟨x₂, hx₂B, hyx₂Inv⟩
      have hyx₁ : ⟪y, x₁⟫ ∈ G := (Inverse.Pair.Spec).1 hyx₁Inv
      have hyx₂ : ⟪y, x₂⟫ ∈ G := (Inverse.Pair.Spec).1 hyx₂Inv
      have hxEq : x₁ = x₂ := function_value_unique G y x₁ x₂ hG hyx₁ hyx₂
      have hx₂A : x₂ ∈ A := by simpa [hxEq] using hx₁A
      exact (Image.Spec).2 ⟨x₂, (Intersection.Spec).2 ⟨hx₂A, hx₂B⟩, hyx₂Inv⟩

  theorem inverse_image_diff (G A B : Set) (hG : IsFunction G) :
      (G⁻¹)⟦A - B⟧ = (G⁻¹)⟦A⟧ - (G⁻¹)⟦B⟧ := by
    apply extensionality
    intro y
    constructor
    · intro h
      rcases (Image.Spec).1 h with ⟨x, hxAB, hyxInv⟩
      rcases (Difference.Spec).1 hxAB with ⟨hxA, hxNotB⟩
      refine (Difference.Spec).2 ?_
      refine ⟨(Image.Spec).2 ⟨x, hxA, hyxInv⟩, ?_⟩
      intro hyB
      rcases (Image.Spec).1 hyB with ⟨x', hx'B, hyx'Inv⟩
      have hyx : ⟪y, x⟫ ∈ G := (Inverse.Pair.Spec).1 hyxInv
      have hyx' : ⟪y, x'⟫ ∈ G := (Inverse.Pair.Spec).1 hyx'Inv
      have hxx' : x = x' := function_value_unique G y x x' hG hyx hyx'
      subst hxx'
      exact hxNotB hx'B
    · intro h
      rcases (Difference.Spec).1 h with ⟨hyA, hyNotB⟩
      rcases (Image.Spec).1 hyA with ⟨x, hxA, hyxInv⟩
      refine (Image.Spec).2 ?_
      refine ⟨x, (Difference.Spec).2 ⟨hxA, ?_⟩, hyxInv⟩
      intro hxB
      apply hyNotB
      exact (Image.Spec).2 ⟨x, hxB, hyxInv⟩

  -- Graph of a Lean-level map restricted to a carrier set.
  noncomputable def GraphOn (A : Set) (f : Set → Set) : Set :=
    Comprehension
      (fun w => ∃ x, x ∈ A ∧ w = ⟨x, f x⟩)
      (A ⨯ A)

  lemma GraphOn.Spec {A : Set} {f : Set → Set} {w : Set} :
      w ∈ GraphOn A f ↔ w ∈ (A ⨯ A) ∧ ∃ x, x ∈ A ∧ w = ⟨x, f x⟩ := by
    simp [GraphOn, Comprehension.Spec]

  lemma GraphOn.Pair.Spec {A : Set} {f : Set → Set} (hf : ∀ x, x ∈ A → f x ∈ A) {x y : Set} :
      OrderedPair x y ∈ GraphOn A f ↔ x ∈ A ∧ y = f x := by
    apply Iff.intro
    · intro hxy
      rcases (GraphOn.Spec).1 hxy with ⟨_, hEx⟩
      rcases hEx with ⟨u, huA, hEq⟩
      rw [OrderedPair.uniqueness] at hEq
      rcases hEq with ⟨hxu, hyf⟩
      subst hxu
      exact And.intro huA hyf
    · intro hxy
      rcases hxy with ⟨hxA, hyEq⟩
      have hxfA : f x ∈ A := hf x hxA
      have hGraph : OrderedPair x (f x) ∈ GraphOn A f := by
        exact (GraphOn.Spec).2
          (And.intro (Pair.mem_product A A x (f x) hxA hxfA) (Exists.intro x (And.intro hxA rfl)))
      simpa [hyEq] using hGraph

  theorem GraphOn.mapsInto (A : Set) (f : Set → Set) (hf : ∀ x, x ∈ A → f x ∈ A) :
      MapsInto (GraphOn A f) A A := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro w hw
        rcases (GraphOn.Spec).1 hw with ⟨_, hEx⟩
        rcases hEx with ⟨x, hxA, hEq⟩
        exact ⟨x, f x, hEq⟩
      · intro x hxDom
        have hxA : x ∈ A := by
          rcases (Relation.Domain.Spec).1 hxDom with ⟨y, hxy⟩
          exact (GraphOn.Pair.Spec hf).1 hxy |>.left
        refine ⟨f x, (GraphOn.Pair.Spec hf).2 (And.intro hxA rfl), ?_⟩
        intro y hxy
        exact (GraphOn.Pair.Spec hf).1 hxy |>.right
    · apply extensionality
      intro x
      apply Iff.intro
      · intro hxDom
        rcases (Relation.Domain.Spec).1 hxDom with ⟨y, hxy⟩
        exact (GraphOn.Pair.Spec hf).1 hxy |>.left
      · intro hxA
        exact (Relation.Domain.Spec).2
          ⟨f x, (GraphOn.Pair.Spec hf).2 (And.intro hxA rfl)⟩
    · intro y hyRan
      rcases (Relation.Range.Spec).1 hyRan with ⟨x, hxy⟩
      rcases (GraphOn.Pair.Spec hf).1 hxy with ⟨hxA, hyEq⟩
      simpa [hyEq] using hf x hxA

  -- Indexed family operations (Enderton p.51 style notation).
  noncomputable def IndexedUnion (F I : Set) : Set :=
    ⋃ (ran (Restriction F I))

  noncomputable def IndexedIntersection (F I : Set) (hFam : (ran (Restriction F I)).Nonempty) : Set :=
    BigIntersection (ran (Restriction F I)) hFam

  -- Function-space object ^A B: all relations on A×B that are maps A -> B.
  noncomputable def FunctionSpace (A B : Set) : Set :=
    Comprehension
      (fun G => G ∈ 𝒫 (A ⨯ B) ∧ MapsInto G A B)
      (𝒫 (𝒫 (A ⨯ B)))

  lemma FunctionSpace.Spec {A B G : Set} :
      G ∈ FunctionSpace A B ↔ G ∈ 𝒫 (𝒫 (A ⨯ B)) ∧ G ∈ 𝒫 (A ⨯ B) ∧ MapsInto G A B := by
    simp [FunctionSpace, Comprehension.Spec]

end Set

