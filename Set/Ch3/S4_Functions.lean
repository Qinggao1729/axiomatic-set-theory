import Set.Ch3.S2_Relations
import Set.Ch2.S2_ArbitraryUnionsIntersections
import Set.SimpAttrs
import Set.Choice

/-!
# Chapter 3, Section 4: Functions

Function definitions and theorems (3E/3F/3G/3H/3I/3K/3L-style results).

The AC-dependent Theorem 3J(b) (right inverse iff onto) is proved at the
bottom of this file, inside a reopened `Choice` namespace. The AC
declarations themselves live in `Set/Choice.lean` (also under
`Set.Choice`); reopening here means the axiom is only in scope inside
that namespace block, and the rest of §Functions is AC-free.
-/

namespace Set
  -- Function [Enderton, p.42]
  def IsFunction (F : Set) : Prop :=
    IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟪x, y⟫ ∈ F

  lemma function_value_unique (F x y z : Set) (hF : IsFunction F) :
      ⟪x, y⟫ ∈ F → ⟪x, z⟫ ∈ F → y = z := by
    intro hxy hxz
    rcases hF with ⟨_, huniq⟩
    have hxdom : x ∈ dom F := Relation.Pair.mem_dom F x y hxy
    rcases huniq x hxdom with ⟨w, hw, hwuniq⟩
    have hyw : y = w := hwuniq y hxy
    have hzw : z = w := hwuniq z hxz
    exact hyw.trans hzw.symm

  -- [Enderton, p.43]
  def MapsInto (F A B : Set) : Prop :=
    IsFunction F ∧ (dom F) = A ∧ (ran F) ⊆ B

  lemma MapsInto.dom_mem_iff (F A B x : Set) :
    MapsInto F A B → (x ∈ (dom F) ↔ x ∈ A) := by
    intro hMap
    rcases hMap with ⟨_, hDomEq, _⟩
    simp [hDomEq]

  -- [Enderton, p.43]
  def MapsOnto (F A B : Set) : Prop :=
    MapsInto F A B ∧ (ran F) = B

  -- A set R is single-rooted iff for each y ∈ ran R there is only one x such that xRy.
  -- [Enderton, p.43]
  def IsSingleRooted (R : Set) : Prop :=
    ∀ (y : Set), y ∈ (ran R) → ∃! (x: Set), ⟪x, y⟫ ∈ R

  -- [Enderton, p.43]
  def IsOneToOne (F : Set) : Prop := IsFunction F ∧ IsSingleRooted F

  -- Single-rooted counterpart of `function_value_unique`: a single-rooted R has
  -- at most one preimage for each y in its range. Used in 3K equality cases
  -- (and 3L) where F is assumed single-rooted instead of a function.
  lemma single_rooted_unique (R x x' y : Set) (hSR : IsSingleRooted R) :
      ⟪x, y⟫ ∈ R → ⟪x', y⟫ ∈ R → x = x' := by
    intro hxy hx'y
    have hyRan : y ∈ ran R := (Range.Spec).2 ⟨x, hxy⟩
    rcases hSR y hyRan with ⟨w, _, huniq⟩
    have hxw : x = w := huniq x hxy
    have hx'w : x' = w := huniq x' hx'y
    exact hxw.trans hx'w.symm


  /-
  Design choice: in Ch3/S4, expose textbook-style "value of a function at x".
  This notation is now used in 3G-style statements/proofs in this file.
  We also define `IsValueAt` here, and plan to prefer that lighter predicate style
  in Ch3/S5 and later sections when statement-level obligations become heavy.
  -/

  -- Value-at predicate: F is a function and ⟪x, y⟫ ∈ F.
  -- Intended as the lighter statement style for Ch3/S5 and onward.
  def IsValueAt (F x y : Set) : Prop :=
    IsFunction F ∧ ⟪x, y⟫ ∈ F


  -- [Enderton, p.43]
  noncomputable def FunctionValue
      (F x : Set) (hF : IsFunction F) (hxdom : x ∈ dom F) : Set :=
    Classical.choose (hF.2 x hxdom)

  -- The "auto" version of FunctionValue, similar to `xs[i]` for lists.
  noncomputable def FunctionValueAuto
      (F x : Set)
      (hF : IsFunction F := by simp_all!)
      (hxdom : x ∈ dom F := by simp_all!) : Set :=
    FunctionValue F x hF hxdom

  notation:max F "⟮" x "⟯" => FunctionValueAuto F x
  syntax:max term "⟮" term "⟯'(" term ")" : term

  -- The "manual" version of FunctionValue, similar to `xs[i]'p` for lists.
  -- Here provide the hypothesis in conjunction to use the ⟨hF, hxdom⟩ syntax.
  noncomputable def FunctionValueWithProof
      (F x : Set) (h : IsFunction F ∧ x ∈ dom F) : Set :=
    FunctionValue F x h.1 h.2

  macro_rules
    | `($F⟮$x⟯'($p)) => `(FunctionValueWithProof $F $x $p)

  lemma FunctionValue.Spec
      (F x : Set) (hF : IsFunction F) (hxdom : x ∈ dom F) :
      ⟪x, F⟮x⟯⟫ ∈ F :=
    (Classical.choose_spec (hF.2 x hxdom)).1

  lemma FunctionValue.eq_of_pair
      (F x y : Set) (hF : IsFunction F)
      (hxy : ⟪x, y⟫ ∈ F) :
      FunctionValue F x hF (Relation.Pair.mem_dom F x y hxy) = y := by
    have hxdom : x ∈ dom F := Relation.Pair.mem_dom F x y hxy
    have huniq : ∀ z, ⟪x, z⟫ ∈ F → z = FunctionValue F x hF hxdom :=
      (Classical.choose_spec (hF.2 x hxdom)).2
    exact (huniq y hxy).symm

  lemma FunctionValueWithProof.eq_of_pair
      (F x y : Set) (h : IsFunction F ∧ x ∈ dom F)
      (hxy : ⟪x, y⟫ ∈ F) :
      F⟮x⟯'(h) = y := by
    simpa [FunctionValueWithProof] using
      (FunctionValue.eq_of_pair F x y h.1 hxy)

  -- #check the AC declarations from `Set/Choice.lean` here, where Enderton
  -- first introduces the first form (p.49). The actual axiom remains
  -- hidden until the `namespace Choice` block at the bottom of this file
  -- reopens the namespace for Theorem 3J(b).
  #check @Choice.ChoiceFirstForm
  #check @Choice.choice_first_form

  -- Enderton didn't explicitly define the Identity function on a set A.
  noncomputable def Identity (A : Set) : Set :=
    Comprehension (λ w ↦ ∃ x, x ∈ A ∧ w = ⟪x, x⟫) (A ⨯ A)

  lemma Identity.Spec {A w : Set} : w ∈ Identity A ↔ w ∈ (A ⨯ A) ∧ ∃ x, x ∈ A ∧ w = ⟪x, x⟫ := by
    simp [Identity, Comprehension.Spec]
  attribute [set_spec_simps] Identity.Spec

  lemma Identity.Pair.Spec {A x y : Set} :
      ⟪x, y⟫ ∈ Identity A ↔ x ∈ A ∧ y = x := by
    constructor
    · intro hxy
      rcases (Identity.Spec).1 hxy with ⟨_, hEx⟩
      rcases hEx with ⟨u, huA, hEq⟩
      rcases (thm_3A_ordered_pair_uniqueness x y u u).1 hEq with ⟨hxu, hyu⟩
      subst hxu
      exact ⟨huA, hyu⟩
    · intro hxy
      rcases hxy with ⟨hxA, hyx⟩
      subst y
      have hProd : ⟪x, x⟫ ∈ (A ⨯ A) := by
        rw [cor_3C_product_spec]
        exact ⟨x, x, hxA, hxA, rfl⟩
      apply (Identity.Spec).2
      exact ⟨hProd, x, hxA, rfl⟩
  attribute [set_spec_simps] Identity.Pair.Spec

  /-
  Function operations [Enderton, p. 44]
  -/
  -- [Enderton, p.44] Inverse relation: F⁻¹ = {⟨u, v⟩ | ⟨v, u⟩ ∈ F}.
  noncomputable def Inverse (F : Set) :=
    Comprehension (λ w ↦ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ w = ⟪v, u⟫) ((ran F) ⨯ (dom F))

  @[simp]
  lemma Inverse.Spec {F x : Set} : x ∈ Inverse F ↔ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ x = ⟪v, u⟫ := by
    rw [Inverse, Comprehension.Spec]
    constructor
    · intro hx
      exact hx.2
    · intro hx
      rcases hx with ⟨u, v, huvF, hxEq⟩
      have hvRan : v ∈ ran F := (Range.Spec).2 ⟨u, huvF⟩
      have huDom : u ∈ dom F := (Domain.Spec).2 ⟨v, huvF⟩
      have hxProd : x ∈ (ran F) ⨯ (dom F) := by
        subst hxEq
        exact (cor_3C_product_spec).2 ⟨v, u, hvRan, huDom, rfl⟩
      exact ⟨hxProd, ⟨u, v, huvF, hxEq⟩⟩
  attribute [set_spec_simps] Inverse.Spec

  @[simp]
  lemma Inverse.Pair.Spec {F x y : Set} : ⟪x, y⟫ ∈ Inverse F ↔ ⟪y, x⟫ ∈ F := by
    rw [Inverse.Spec]
    constructor
    · intro h
      rcases h with ⟨u, v, huv, hEq⟩
      rcases (thm_3A_ordered_pair_uniqueness x y v u).1 hEq with ⟨hxv, hyu⟩
      subst hxv hyu
      exact huv
    · intro h
      exact ⟨y, x, h, rfl⟩
  attribute [set_spec_simps] Inverse.Pair.Spec

  postfix:90 "⁻¹" => Inverse

  -- [Enderton, p.44] Composition: F ∘ G = {⟨u, v⟩ | ∃ t, ⟨u, t⟩ ∈ G ∧ ⟨t, v⟩ ∈ F}.
  noncomputable def Composition (F G : Set) :=
    Comprehension
      (λ w ↦ ∃ (u v t : Set), ⟪u, t⟫ ∈ G ∧ ⟪t, v⟫ ∈ F ∧ w = ⟪u, v⟫)
      ((dom G) ⨯ (ran F))

  @[simp]
  lemma Composition.Spec {F G x : Set} : x ∈ Composition F G ↔ (x ∈ ((dom G) ⨯ (ran F))) ∧ ∃ (u v t : Set), ⟪u, t⟫ ∈ G ∧ ⟪t, v⟫ ∈ F ∧ x = ⟪u, v⟫ := by
    simp [Composition, Comprehension.Spec]
  attribute [set_spec_simps] Composition.Spec

  @[simp]
  lemma Composition.Pair.Spec {F G x y : Set} :
      ⟪x, y⟫ ∈ Composition F G ↔ ∃ t, ⟪x, t⟫ ∈ G ∧ ⟪t, y⟫ ∈ F := by
    rw [Composition.Spec]
    constructor
    · intro h
      rcases h with ⟨_, u, v, t, hu, hv, hEq⟩
      rcases (thm_3A_ordered_pair_uniqueness x y u v).1 hEq with ⟨hxu, hyv⟩
      subst hxu hyv
      exact ⟨t, hu, hv⟩
    · intro h
      rcases h with ⟨t, hxt, hty⟩
      have hxDom : x ∈ dom G := (Domain.Spec).2 ⟨t, hxt⟩
      have hyRan : y ∈ ran F := (Range.Spec).2 ⟨t, hty⟩
      have hProd : ⟪x, y⟫ ∈ (dom G) ⨯ (ran F) :=
        (cor_3C_product_spec).2 ⟨x, y, hxDom, hyRan, rfl⟩
      exact ⟨hProd, x, y, t, hxt, hty, rfl⟩
  attribute [set_spec_simps] Composition.Pair.Spec

  infixr:90 " ∘ " => Composition

  -- [Enderton, p.44] Restriction: F ↾ C = {⟨u, v⟩ ∈ F | u ∈ C}.
  noncomputable def Restriction (F : Set) (C : Set) :=
    Comprehension (λ w ↦ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ u ∈ C ∧ w = ⟪u, v⟫) F

  @[simp]
  lemma Restriction.Spec {F C w : Set} : w ∈ Restriction F C ↔ w ∈ F ∧ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ u ∈ C ∧ w = ⟪u, v⟫ := by
    simp [Restriction, Comprehension.Spec]
  attribute [set_spec_simps] Restriction.Spec

  @[simp]
  lemma Restriction.Pair.Spec {F C u v : Set} : ⟪u, v⟫ ∈ Restriction F C ↔ ⟪u, v⟫ ∈ F ∧ u ∈ C := by
    rw [Restriction.Spec]
    constructor
    · intro h
      rcases h with ⟨hF, x, y, hxy, hxC, hEq⟩
      rcases (thm_3A_ordered_pair_uniqueness u v x y).1 hEq with ⟨hux, hvy⟩
      subst hux hvy
      exact ⟨hxy, hxC⟩
    · intro h
      rcases h with ⟨hF, hC⟩
      exact ⟨hF, u, v, hF, hC, rfl⟩
  attribute [set_spec_simps] Restriction.Pair.Spec

  infixr:90 " ↾ " => Restriction

  -- [Enderton, p.44] Image: F⟦C⟧ = {y | ∃ u ∈ C, ⟨u, y⟩ ∈ F} = ran(F ↾ C).
  -- Image is not a relation, so no Image.Pair.Spec
  noncomputable def Image (F : Set) (C : Set) :=
    ran (Restriction F C)
  notation:90 F "⟦" A "⟧" => Image F A

  @[simp]
  lemma Image.Spec {F C y : Set} : y ∈ F⟦C⟧ ↔ ∃ u, u ∈ C ∧ ⟪u, y⟫ ∈ F := by
    rw [Image, Range.Spec]
    constructor
    · intro h
      rcases h with ⟨u, hu⟩
      rw [Restriction.Pair.Spec] at hu
      exact ⟨u, hu.right, hu.left⟩
    · intro h
      rcases h with ⟨u, huC, huF⟩
      exact ⟨u, (Restriction.Pair.Spec).2 ⟨huF, huC⟩⟩
  attribute [set_spec_simps] Image.Spec

  /-
  [Enderton, Theorem 3E, p. 46]
  For a set F, dom F⁻¹ = ran F and ran F⁻¹ = dom F. For a relation F, (F⁻¹)⁻¹ = F.
  -/
  theorem thm_3E_domain_inverse (F : Set) : (dom (F⁻¹)) = ran F := by
    apply extensionality
    intro x
    apply Iff.intro
    · intro h
      rw [Domain.Spec] at h
      obtain ⟨y, hy⟩ := h
      apply (Range.Spec).2
      exists y
      exact (Inverse.Pair.Spec).1 hy
    · intro h
      rcases (Range.Spec).1 h with ⟨y, hyx⟩
      apply (Domain.Spec).2
      exists y
      exact (Inverse.Pair.Spec).2 hyx

  theorem thm_3E_range_inverse (F : Set) : (ran (Inverse F)) = dom F := by
    apply extensionality
    intro x
    apply Iff.intro
    · intro h
      rw [Range.Spec] at h
      obtain ⟨y, hy⟩ := h
      have hxy : ⟪x, y⟫ ∈ F := (Inverse.Pair.Spec).1 hy
      apply (Domain.Spec).2
      exact ⟨y, hxy⟩
    · intro h
      rcases (Domain.Spec).1 h with ⟨y, hxy⟩
      apply (Range.Spec).2
      have hxyInv : ⟪y, x⟫ ∈ F⁻¹ := (Inverse.Pair.Spec).2 hxy
      exact ⟨y, hxyInv⟩

  theorem thm_3E_relation_inverse_inverse (F : Set) {hF : IsRelation F} : ((F⁻¹)⁻¹) = F := by
    apply extensionality
    intro x
    apply Iff.intro
    · intro hx
      rcases (Inverse.Spec).1 hx with ⟨u, v, huv, rfl⟩
      exact (Inverse.Pair.Spec).1 huv
    · intro hx
      rcases hF x hx with ⟨u, v, rfl⟩
      have hvu : ⟪v, u⟫ ∈ Inverse F := (Inverse.Pair.Spec).2 hx
      exact (Inverse.Pair.Spec).2 hvu

  lemma preimage_dom (F : Set) (y : Set) (hy : y ∈ ran F) : y ∈ dom (F⁻¹) := by
    simpa [thm_3E_domain_inverse] using hy


  /-
  [Enderton, Theorem 3F, p. 46]
  For a set F, F⁻¹ is a function iff F is single-rooted. A relation F is a function iff F⁻¹ is single-rooted.
  -/
  theorem thm_3F_inverse_single_rooted (F : Set) : IsFunction (Inverse F) ↔ IsSingleRooted F := by
    apply Iff.intro
    · intro hFi
      rw [IsFunction, thm_3E_domain_inverse] at hFi
      obtain ⟨_, hFi⟩ := hFi
      rw [IsSingleRooted]
      intro x hx
      obtain ⟨y, hxyInv, huniq⟩ := hFi x hx
      refine ⟨y, (Inverse.Pair.Spec).1 hxyInv, ?_⟩
      intro y' hy'xF
      have hxy'Inv : ⟪x, y'⟫ ∈ Inverse F := (Inverse.Pair.Spec).2 hy'xF
      exact huniq y' hxy'Inv
    · -- IsSingleRooted F → F⁻¹ is a function
      intro h
      rw [IsSingleRooted] at h
      apply And.intro
      · -- Show: F⁻¹ is a relation
        rw [IsRelation]
        intro w hw
        rcases (Inverse.Spec).1 hw with ⟨u, v, _, hEq⟩
        exact ⟨v, u, hEq⟩
      · -- Show: uniqueness of function values
        intro x hx
        rw [thm_3E_domain_inverse] at hx
        obtain ⟨y, hyxF, hyuniq⟩ := h x hx
        refine ⟨y, (Inverse.Pair.Spec).2 hyxF, ?_⟩
        intro y' hy'
        have hy'xF : ⟪y', x⟫ ∈ F := (Inverse.Pair.Spec).1 hy'
        exact hyuniq y' hy'xF


  theorem thm_3F_relation_function_single_rooted (F : Set) {hR : IsRelation F} : IsFunction F ↔ IsSingleRooted (Inverse F) := by
    have hInv : IsFunction ((F⁻¹)⁻¹) ↔ IsSingleRooted (F⁻¹) :=
      thm_3F_inverse_single_rooted (F⁻¹)
    simpa [thm_3E_relation_inverse_inverse (F := F) (hF := hR)] using hInv

  lemma inv_is_function (F : Set) : IsOneToOne F → IsFunction (F⁻¹) := by
    intro hOne
    exact (thm_3F_inverse_single_rooted F).2 hOne.2

  /-
  [Enderton, Theorem 3G, p. 46]
  Assume that F is a one-to-one function. If x ∈ dom F, then F⁻¹(F(x)) = x. If y ∈ ran F, then F(F⁻¹(y)) = y.
  -/
  lemma image_mem_dom_inverse
      (F : Set) (hF : IsFunction F) (x : Set) (hx : x ∈ dom F) :
      F⟮x⟯ ∈ dom (F⁻¹) := by
    have hxy : ⟪x, F⟮x⟯⟫ ∈ F := by
      simpa using FunctionValue.Spec F x hF hx
    exact (Domain.Spec).2 ⟨x, (Inverse.Pair.Spec).2 hxy⟩

  lemma preimage_mem_dom
      (F : Set) (hInv : IsFunction (F⁻¹)) (y : Set) (hy : y ∈ ran F) :
      (F⁻¹)⟮y⟯'(⟨hInv, preimage_dom F y hy⟩) ∈ dom F := by
    have hyxInv : ⟪y, (F⁻¹)⟮y⟯'(⟨hInv, preimage_dom F y hy⟩)⟫ ∈ F⁻¹ := by
      simpa using FunctionValue.Spec (F⁻¹) y
        hInv (preimage_dom F y hy)
    have hxy : ⟪(F⁻¹)⟮y⟯'(⟨hInv, preimage_dom F y hy⟩), y⟫ ∈ F :=
      (Inverse.Pair.Spec).1 hyxInv
    exact Relation.Pair.mem_dom F _ y hxy

  theorem thm_3G_one_to_one_inverse (F : Set) :
      ∀ hOne : IsOneToOne F,
      ∀ x, ∀ hx : x ∈ dom F,
      F⁻¹⟮F⟮x⟯'(⟨hOne.1, hx⟩)⟯'(
        ⟨(inv_is_function F hOne),
        (image_mem_dom_inverse F hOne.1 x hx)⟩)
      = x := by
    intro hOne x hx
    have hF : IsFunction F := hOne.1 -- for automatic version of FunctionValue
    have hxy : ⟪x, F⟮x⟯⟫ ∈ F := by
      simpa using FunctionValue.Spec F x hOne.1 hx
    have hyxInv : ⟪F⟮x⟯, x⟫ ∈ F⁻¹ := (Inverse.Pair.Spec).2 hxy
    exact FunctionValue.eq_of_pair
      (F := F⁻¹)
      (x := F⟮x⟯)
      (y := x)
      (inv_is_function F hOne)
      hyxInv

  theorem thm_3G_one_to_one_inverse_ran (F : Set) :
      ∀ hOne : IsOneToOne F,
      ∀ y, ∀ hy : y ∈ ran F,
      F ⟮F⁻¹⟮y⟯'(⟨inv_is_function F hOne, preimage_dom F y hy⟩)⟯'(
        ⟨hOne.1,
        (preimage_mem_dom F (inv_is_function F hOne) y hy)⟩)
      = y := by
    intro hOne y hy
    have hinvfunc : F⁻¹.IsFunction := inv_is_function F hOne
    have hydominv : y ∈ dom F⁻¹ := preimage_dom F y hy
    have hyxInv : ⟪y, F⁻¹⟮y⟯⟫ ∈ F⁻¹ := by
      simpa using FunctionValue.Spec (F⁻¹) y hinvfunc hydominv
    have hxy : ⟪F⁻¹⟮y⟯, y⟫ ∈ F := (Inverse.Pair.Spec).1 hyxInv
    exact FunctionValue.eq_of_pair
      (F := F)
      (x := FunctionValue (F⁻¹) y hinvfunc hydominv)
      (y := y)
      hOne.1
      hxy

  /-
  [Enderton, Theorem 3H, p. 47]
  If F and G are functions, then F ∘ G is a function.
  -/
  theorem thm_3H_composition_is_function (F G : Set) : IsFunction F → IsFunction G → IsFunction (Composition F G) := by
    intro hF hG
    apply And.intro
    · intro w hw
      rw [Composition.Spec] at hw
      rcases hw with ⟨_, u, v, _, _, _, hEq⟩
      exact ⟨u, v, hEq⟩
    · intro x hx
      rw [Domain.Spec] at hx
      rcases hx with ⟨y, hxy⟩
      rcases (Composition.Pair.Spec).1 hxy with ⟨t, hxt, hty⟩
      refine ⟨y, hxy, ?_⟩
      intro y' hxy'
      rcases (Composition.Pair.Spec).1 hxy' with ⟨t', hxt', ht'y'⟩
      have htt' : t = t' := function_value_unique G x t t' hG hxt hxt'
      subst htt'
      exact (function_value_unique F t y y' hF hty ht'y').symm

  noncomputable def CompositionDomain (F G : Set) : Set :=
    Comprehension (λ x ↦ ∃ t, ⟪x, t⟫ ∈ G ∧ t ∈ (dom F)) (dom G)

  lemma CompositionDomain.Spec {F G x : Set} :
      x ∈ CompositionDomain F G ↔ x ∈ (dom G) ∧ ∃ t, ⟪x, t⟫ ∈ G ∧ t ∈ (dom F) := by
    simp [CompositionDomain, Comprehension.Spec]

  theorem thm_3H_composition_domain (F G : Set) :
      Domain (Composition F G) = CompositionDomain F G := by
    apply extensionality
    intro x
    apply Iff.intro
    · intro hx
      rw [Domain.Spec] at hx
      rcases hx with ⟨y, hxy⟩
      rcases (Composition.Pair.Spec).1 hxy with ⟨t, hxt, hty⟩
      rw [CompositionDomain.Spec]
      exact ⟨Relation.Pair.mem_dom G x t hxt, t, hxt, Relation.Pair.mem_dom F t y hty⟩
    · intro hx
      rw [CompositionDomain.Spec] at hx
      rcases hx with ⟨_, t, hxt, htDomF⟩
      rw [Domain.Spec] at htDomF
      rcases htDomF with ⟨y, hty⟩
      rw [Domain.Spec]
      exact ⟨y, (Composition.Pair.Spec).2 ⟨t, hxt, hty⟩⟩

  /-
  [Enderton, Theorem 3H continued, p. 47]
  For all x ∈ dom (F ∘ G), (F ∘ G)(x) = F(G(x)).

  The two helper lemmas below derive `x ∈ dom G` and `G(x) ∈ dom F`
  from `x ∈ dom (F ∘ G)`; they are needed to validate the `F(G(x))`
  notation in the main statement.
  -/
  lemma comp_dom_mem_inner_dom (F G x : Set) (hx : x ∈ dom (Composition F G)) :
      x ∈ dom G := by
    rw [thm_3H_composition_domain, CompositionDomain.Spec] at hx
    exact hx.1

  lemma comp_value_mem_outer_dom (F G x : Set) (hG : IsFunction G)
      (hx : x ∈ dom (Composition F G)) :
      G⟮x⟯'(⟨hG, comp_dom_mem_inner_dom F G x hx⟩) ∈ dom F := by
    have hxCD : x ∈ CompositionDomain F G := by
      rw [← thm_3H_composition_domain]; exact hx
    rcases (CompositionDomain.Spec).1 hxCD with ⟨_, t, hxt, htDomF⟩
    have hGxG : ⟪x, G⟮x⟯'(⟨hG, comp_dom_mem_inner_dom F G x hx⟩)⟫ ∈ G := by
      simpa [FunctionValueWithProof] using
        FunctionValue.Spec G x hG (comp_dom_mem_inner_dom F G x hx)
    have hGx_eq_t : G⟮x⟯'(⟨hG, comp_dom_mem_inner_dom F G x hx⟩) = t :=
      function_value_unique G x _ t hG hGxG hxt
    rw [hGx_eq_t]
    exact htDomF

  theorem thm_3H_composition_value_equal
      (F G x : Set) (hF : IsFunction F) (hG : IsFunction G)
      (hx : x ∈ dom (F ∘ G)) :
      (F ∘ G)⟮x⟯'(⟨thm_3H_composition_is_function F G hF hG, hx⟩)
      = F⟮G⟮x⟯'(⟨hG, comp_dom_mem_inner_dom F G x hx⟩)⟯'(
          ⟨hF, comp_value_mem_outer_dom F G x hG hx⟩) := by
    have hxDomG : x ∈ dom G := comp_dom_mem_inner_dom F G x hx
    have hGxDomF : G⟮x⟯ ∈ dom F := comp_value_mem_outer_dom F G x hG hx
    have hxG : ⟪x, G⟮x⟯⟫ ∈ G := by
      simpa using FunctionValue.Spec G x hG hxDomG
    have hGxF : ⟪G⟮x⟯, F⟮G⟮x⟯⟯⟫ ∈ F := by
      simpa using FunctionValue.Spec F G⟮x⟯ hF hGxDomF
    have hxFG : ⟪x, F⟮G⟮x⟯⟯⟫ ∈ F ∘ G :=
      (Composition.Pair.Spec).2 ⟨_, hxG, hGxF⟩
    exact FunctionValueWithProof.eq_of_pair (Composition F G) x _
      ⟨thm_3H_composition_is_function F G hF hG, hx⟩ hxFG

  /-
  [Enderton, Theorem 3I / 3I in our todo numbering]
  (F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹
  -/
  theorem thm_3I_inverse_composition (F G : Set) : (Composition F G)⁻¹ = Composition (Inverse G) (Inverse F) := by
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

  /-
  [Enderton, Theorem 3K, p. 50] auxiliary construction.
  The family `{F⟦A⟧ | A ∈ 𝒜}` used in the second halves of 3K(a)(b)
  and throughout 3L. Each member is a subset of `ran F`, so the carrier
  `𝒫 (ran F)` is sufficient.
  -/
  noncomputable def ImageFamily (F 𝒜 : Set) : Set :=
    Comprehension (fun w => ∃ A, A ∈ 𝒜 ∧ w = F⟦A⟧) (𝒫 (ran F))

  lemma ImageFamily.Spec {F 𝒜 w : Set} :
      w ∈ ImageFamily F 𝒜 ↔ ∃ A, A ∈ 𝒜 ∧ w = F⟦A⟧ := by
    simp only [ImageFamily, Comprehension.Spec, Power.Spec]
    constructor
    · rintro ⟨_, A, hA, hw⟩
      exact ⟨A, hA, hw⟩
    · rintro ⟨A, hA, hw⟩
      refine ⟨?_, A, hA, hw⟩
      subst hw
      intro y hyImg
      rcases (Image.Spec).1 hyImg with ⟨u, _, huy⟩
      exact (Range.Spec).2 ⟨u, huy⟩
  attribute [set_spec_simps] ImageFamily.Spec

  lemma ImageFamily.Nonempty {F 𝒜 : Set} (h𝒜 : 𝒜.Nonempty) :
      (ImageFamily F 𝒜).Nonempty := by
    rcases h𝒜 with ⟨A, hA⟩
    exact ⟨F⟦A⟧, (ImageFamily.Spec).2 ⟨A, hA, rfl⟩⟩

  /-
  [Enderton, Theorem 3K(a), p. 50]
  The image of a union is the union of the images, in both the binary form
  `F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧` and the arbitrary form
  `F⟦⋃𝒜⟧ = ⋃{F⟦A⟧ | A ∈ 𝒜}`. F need not be a function.
  -/
  theorem thm_3Ka_image_union (F A B : Set) : F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧ := by
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

  theorem thm_3Ka_image_bigUnion (F 𝒜 : Set) :
      F⟦⋃ 𝒜⟧ = ⋃ (ImageFamily F 𝒜) := by
    apply extensionality
    intro y
    constructor
    · intro hy
      rcases (Image.Spec).1 hy with ⟨x, hxBU, hxy⟩
      rcases (BigUnion.Spec).1 hxBU with ⟨A, hA𝒜, hxA⟩
      refine (BigUnion.Spec).2 ⟨F⟦A⟧, ?_, ?_⟩
      · exact (ImageFamily.Spec).2 ⟨A, hA𝒜, rfl⟩
      · exact (Image.Spec).2 ⟨x, hxA, hxy⟩
    · intro hy
      rcases (BigUnion.Spec).1 hy with ⟨B, hBfam, hyB⟩
      rcases (ImageFamily.Spec).1 hBfam with ⟨A, hA𝒜, hBeq⟩
      subst hBeq
      rcases (Image.Spec).1 hyB with ⟨x, hxA, hxy⟩
      refine (Image.Spec).2 ⟨x, ?_, hxy⟩
      exact (BigUnion.Spec).2 ⟨A, hA𝒜, hxA⟩

  /-
  [Enderton, Theorem 3K(b), p. 50]
  The image of an intersection is included in the intersection of the images,
  in both the binary form `F⟦A ∩ B⟧ ⊆ F⟦A⟧ ∩ F⟦B⟧` and the arbitrary form
  `F⟦⋂𝒜⟧ ⊆ ⋂{F⟦A⟧ | A ∈ 𝒜}` (𝒜 nonempty). Equality holds when F is
  single-rooted; that direction is recorded as a separate theorem.
  -/
  theorem thm_3Kb_image_inter_subset (F A B : Set) : F⟦A ∩ B⟧ ⊆ F⟦A⟧ ∩ F⟦B⟧ := by
    intro y hy
    rw [Image.Spec] at hy
    rcases hy with ⟨x, hxAB, hxy⟩
    rw [Intersection.Spec] at hxAB
    rw [Intersection.Spec, Image.Spec, Image.Spec]
    exact ⟨⟨x, hxAB.left, hxy⟩, ⟨x, hxAB.right, hxy⟩⟩

  theorem thm_3Kb_image_bigInter_subset
      (F 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) :
      F⟦BigIntersection 𝒜 h𝒜⟧
      ⊆ BigIntersection (ImageFamily F 𝒜) (ImageFamily.Nonempty h𝒜) := by
    intro y hy
    rcases (Image.Spec).1 hy with ⟨x, hxBI, hxy⟩
    refine (BigIntersection.Spec (ImageFamily.Nonempty h𝒜)).2 ?_
    intro B hBfam
    rcases (ImageFamily.Spec).1 hBfam with ⟨A, hA𝒜, hBeq⟩
    subst hBeq
    refine (Image.Spec).2 ⟨x, ?_, hxy⟩
    exact (BigIntersection.Spec h𝒜).1 hxBI A hA𝒜

  theorem thm_3Kb_image_inter_eq_of_single_rooted
      (F A B : Set) (hSR : IsSingleRooted F) :
      F⟦A ∩ B⟧ = F⟦A⟧ ∩ F⟦B⟧ := by
    apply extensionality
    intro y
    constructor
    · intro hy
      exact thm_3Kb_image_inter_subset F A B y hy
    · intro hy
      rcases (Intersection.Spec).1 hy with ⟨hyA, hyB⟩
      rcases (Image.Spec).1 hyA with ⟨x₁, hx₁A, hxy₁⟩
      rcases (Image.Spec).1 hyB with ⟨x₂, hx₂B, hxy₂⟩
      have hxEq : x₁ = x₂ := single_rooted_unique F x₁ x₂ y hSR hxy₁ hxy₂
      have hx₁B : x₁ ∈ B := by rw [hxEq]; exact hx₂B
      exact (Image.Spec).2 ⟨x₁, (Intersection.Spec).2 ⟨hx₁A, hx₁B⟩, hxy₁⟩

  theorem thm_3Kb_image_bigInter_eq_of_single_rooted
      (F 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) (hSR : IsSingleRooted F) :
      F⟦BigIntersection 𝒜 h𝒜⟧
      = BigIntersection (ImageFamily F 𝒜) (ImageFamily.Nonempty h𝒜) := by
    apply extensionality
    intro y
    constructor
    · intro hy
      exact thm_3Kb_image_bigInter_subset F 𝒜 h𝒜 y hy
    · intro hy
      -- y belongs to every F⟦A⟧ for A ∈ 𝒜.
      have hAll : ∀ A, A ∈ 𝒜 → y ∈ F⟦A⟧ := by
        intro A hA𝒜
        have hFAfam : F⟦A⟧ ∈ ImageFamily F 𝒜 :=
          (ImageFamily.Spec).2 ⟨A, hA𝒜, rfl⟩
        exact (BigIntersection.Spec (ImageFamily.Nonempty h𝒜)).1 hy (F⟦A⟧) hFAfam
      -- Fix a base witness x₀ from some A₀ ∈ 𝒜 (without losing h𝒜).
      have hWit : ∃ A, A ∈ 𝒜 := h𝒜
      rcases hWit with ⟨A₀, hA₀⟩
      rcases (Image.Spec).1 (hAll A₀ hA₀) with ⟨x₀, _, hxy₀⟩
      refine (Image.Spec).2 ⟨x₀, ?_, hxy₀⟩
      refine (BigIntersection.Spec h𝒜).2 ?_
      intro A hA𝒜
      rcases (Image.Spec).1 (hAll A hA𝒜) with ⟨x, hxA, hxy⟩
      have hxEq : x = x₀ := single_rooted_unique F x x₀ y hSR hxy hxy₀
      rw [hxEq] at hxA
      exact hxA

  /-
  [Enderton, Theorem 3K(c), p. 50]
  The image of a difference includes the difference of the images:
  `F⟦A⟧ - F⟦B⟧ ⊆ F⟦A - B⟧`. Equality holds when F is single-rooted.
  -/
  theorem thm_3Kc_image_diff_subset (F A B : Set) : F⟦A⟧ - F⟦B⟧ ⊆ F⟦A - B⟧ := by
    intro y hy
    rw [Difference.Spec, Image.Spec] at hy
    rcases hy with ⟨⟨x, hxA, hxy⟩, hyNotB⟩
    have hxNotB : x ∉ B := by
      intro hxB
      apply hyNotB
      exact (Image.Spec).2 ⟨x, hxB, hxy⟩
    exact (Image.Spec).2 ⟨x, (Difference.Spec).2 ⟨hxA, hxNotB⟩, hxy⟩

  theorem thm_3Kc_image_diff_eq_of_single_rooted
      (F A B : Set) (hSR : IsSingleRooted F) :
      F⟦A⟧ - F⟦B⟧ = F⟦A - B⟧ := by
    apply extensionality
    intro y
    constructor
    · intro hy
      exact thm_3Kc_image_diff_subset F A B y hy
    · intro hy
      rcases (Image.Spec).1 hy with ⟨x, hxAB, hxy⟩
      rcases (Difference.Spec).1 hxAB with ⟨hxA, hxNotB⟩
      refine (Difference.Spec).2 ⟨?_, ?_⟩
      · exact (Image.Spec).2 ⟨x, hxA, hxy⟩
      · intro hyImgB
        rcases (Image.Spec).1 hyImgB with ⟨x', hx'B, hx'y⟩
        have hxEq : x = x' := single_rooted_unique F x x' y hSR hxy hx'y
        rw [hxEq] at hxNotB
        exact hxNotB hx'B

  /-
  [Enderton, Corollary 3L, p. 51]
  For any function G, the inverse image preserves arbitrary unions,
  arbitrary nonempty intersections, and binary differences. Each part is the
  single-rooted equality form of Theorem 3K specialized to `G⁻¹`, since the
  inverse of a function is always single-rooted (Theorem 3F).
  -/
  private lemma inverse_single_rooted_of_function
      {G : Set} (hG : IsFunction G) : IsSingleRooted (G⁻¹) :=
    (@thm_3F_relation_function_single_rooted G hG.1).1 hG

  theorem cor_3La_inverse_image_bigUnion (G 𝒜 : Set) :
      (G⁻¹)⟦⋃ 𝒜⟧ = ⋃ (ImageFamily (G⁻¹) 𝒜) := by
    exact thm_3Ka_image_bigUnion (G⁻¹) 𝒜

  theorem cor_3Lb_inverse_image_bigInter
      (G 𝒜 : Set) (hG : IsFunction G) (h𝒜 : 𝒜.Nonempty) :
      (G⁻¹)⟦BigIntersection 𝒜 h𝒜⟧
      = BigIntersection (ImageFamily (G⁻¹) 𝒜) (ImageFamily.Nonempty h𝒜) := by
    exact thm_3Kb_image_bigInter_eq_of_single_rooted (G⁻¹) 𝒜 h𝒜
      (inverse_single_rooted_of_function hG)

  theorem cor_3Lc_inverse_image_diff
      (G A B : Set) (hG : IsFunction G) :
      (G⁻¹)⟦A - B⟧ = (G⁻¹)⟦A⟧ - (G⁻¹)⟦B⟧ := by
    exact (thm_3Kc_image_diff_eq_of_single_rooted (G⁻¹) A B
      (inverse_single_rooted_of_function hG)).symm

  /-
  Indexed family operations [Enderton, p. 51].
  Enderton's setup: `F` is a function whose domain includes `I`. The union
  `⋃_{i ∈ I} F(i)` is defined unconditionally; the intersection
  `⋂_{i ∈ I} F(i)` requires the additional hypothesis that `I` is nonempty.

  We state `IndexedUnion` without preconditions (the set-theoretic
  definition makes sense for any `F`, `I`), and for `IndexedIntersection`
  expose `I.Nonempty` as the headline Enderton-style precondition together
  with `I ⊆ dom F`, which is the part of "F is a function whose domain
  includes I" actually needed to make the resulting family nonempty.
  -/
  noncomputable def IndexedUnion (F I : Set) : Set :=
    ⋃ (ran (Restriction F I))

  -- When `I` is nonempty and `I ⊆ dom F`, the range of `F ↾ I` is nonempty.
  lemma restriction_range_nonempty
      {F I : Set} (hI : I.Nonempty) (hDom : I ⊆ dom F) :
      (ran (Restriction F I)).Nonempty := by
    rcases hI with ⟨i, hi⟩
    rcases (Domain.Spec).1 (hDom i hi) with ⟨y, hxy⟩
    exact ⟨y, (Range.Spec).2 ⟨i, (Restriction.Pair.Spec).2 ⟨hxy, hi⟩⟩⟩

  noncomputable def IndexedIntersection
      (F I : Set) (hI : I.Nonempty) (hDom : I ⊆ dom F) : Set :=
    BigIntersection (ran (Restriction F I))
      (restriction_range_nonempty hI hDom)

  /-
  Function-space object `ᴬB` [Enderton, p. 52].
  Enderton's justification: if `F : A → B` then `F ⊆ A × B`, so
  `F ∈ 𝒫(A × B)`; apply a subset axiom to `𝒫(A × B)`.
  Hence the carrier is `𝒫(A ⨯ B)` (single power set), and the predicate
  is exactly `MapsInto G A B`.
  -/
  noncomputable def FunctionSpace (A B : Set) : Set :=
    Comprehension (fun G => MapsInto G A B) (𝒫 (A ⨯ B))

  lemma FunctionSpace.Spec {A B G : Set} :
      G ∈ FunctionSpace A B ↔ G ⊆ (A ⨯ B) ∧ MapsInto G A B := by
    simp [FunctionSpace, Comprehension.Spec]

  /-
  Theorem 3J [Enderton, pp. 48–49].

  Part (a) is AC-free; part (b) is the textbook's first appeal to the
  Axiom of Choice. We therefore prove (a) (and its supporting construction
  `LeftInverseRelation` + `one_to_one_preimage_unique`) in the plain
  `Set` namespace, and put **only** 3J(b) inside a reopened `namespace
  Choice` block where `choice_first_form` is in scope. The rule of thumb
  driving this split: a declaration lives in `Choice` iff its proof
  actually uses an AC axiom.

  `aesop` is permitted in this section (per project rule) for routine
  membership/case bookkeeping; we still keep the high-level structure
  explicit.
  -/

  /-- Two preimages of the same element in a one-to-one function coincide.
  AC-free helper used by both 3J(a) and 3J(b). -/
  lemma one_to_one_preimage_unique (F x z y : Set) (hInj : IsOneToOne F)
      (hxy : ⟪x, y⟫ ∈ F) (hzy : ⟪z, y⟫ ∈ F) : x = z := by
    rcases hInj with ⟨_, hSR⟩
    have hyRan : y ∈ ran F := Relation.Pair.mem_ran F x y hxy
    rcases hSR y hyRan with ⟨w, _, huniq⟩
    have hxw : x = w := huniq x hxy
    have hzw : z = w := huniq z hzy
    exact hxw.trans hzw.symm

  /--
  Enderton's "extend `F⁻¹` to all of `B`" construction (Theorem 3J(a) proof).
  On `ran F` it agrees with `F⁻¹`; on `B - ran F` it pairs every element
  with the fixed `a₀ ∈ A`. AC is not needed: the extension is fully
  determined by `a₀`.
  -/
  noncomputable def LeftInverseRelation (F B a0 : Set) : Set :=
    (F⁻¹) ∪ ((B - ran F) ⨯ Singleton a0)

  lemma LeftInverseRelation.Spec {F B a0 u v : Set} :
      ⟪u, v⟫ ∈ LeftInverseRelation F B a0 ↔
        (⟪u, v⟫ ∈ F⁻¹ ∨ (u ∈ (B - ran F) ∧ v = a0)) := by
    constructor
    · intro huv
      rw [LeftInverseRelation, Union.Spec] at huv
      cases huv with
      | inl hInv => exact Or.inl hInv
      | inr hDef =>
        rcases (Product.Spec).1 hDef with ⟨x, y, hxDiff, hySing, hEq⟩
        rcases (OrderedPair.uniqueness u v x y).1 hEq with ⟨hux, hvy⟩
        subst hux
        have hvSing : v ∈ Singleton a0 := by simpa [hvy] using hySing
        exact Or.inr ⟨hxDiff, (Singleton.Spec).1 hvSing⟩
    · intro huv
      rw [LeftInverseRelation, Union.Spec]
      cases huv with
      | inl hInv => exact Or.inl hInv
      | inr hDef =>
        rcases hDef with ⟨huDiff, hvEq⟩
        have hvSing : v ∈ Singleton a0 := by
          rw [Singleton.Spec]; exact hvEq
        exact Or.inr ((Product.Pair.Spec).2 ⟨huDiff, hvSing⟩)

  /-
  [Enderton, Theorem 3J(a), p. 48]
  For `F : A → B` with `A` nonempty, there is a left inverse `G : B → A`
  with `G ∘ F = I_A` iff `F` is one-to-one. **AC-free** — the (⇒) direction
  uses `LeftInverseRelation`, which is fully determined once a fixed
  `a₀ ∈ A` is picked.
  -/
  theorem thm_3J_a_left_inverse_iff_one_to_one
      (F A B : Set) (hMap : MapsInto F A B) (hANon : A.Nonempty) :
      (∃ G, MapsInto G B A ∧ (G ∘ F) = Identity A) ↔ IsOneToOne F := by
    rcases hMap with ⟨hFfun, hDomF, hRanSub⟩
    constructor
    · -- (←) Left-inverse `G` collapses preimages of every `y ∈ ran F`.
      rintro ⟨G, ⟨hGfun, hDomG, _⟩, hComp⟩
      refine ⟨hFfun, ?_⟩
      intro y hyRan
      rcases (Range.Spec).1 hyRan with ⟨x, hxy⟩
      refine ⟨x, hxy, ?_⟩
      intro z hzy
      have hyB : y ∈ B := hRanSub y hyRan
      have hyDomG : y ∈ dom G := by simpa [hDomG] using hyB
      rcases hGfun.2 y hyDomG with ⟨t, hyt, _⟩
      have hxt : ⟪x, t⟫ ∈ Identity A := by
        have : ⟪x, t⟫ ∈ G ∘ F := (Composition.Pair.Spec).2 ⟨y, hxy, hyt⟩
        simpa [hComp] using this
      have hzt : ⟪z, t⟫ ∈ Identity A := by
        have : ⟪z, t⟫ ∈ G ∘ F := (Composition.Pair.Spec).2 ⟨y, hzy, hyt⟩
        simpa [hComp] using this
      have htx : t = x := ((Identity.Pair.Spec).1 hxt).2
      have htz : t = z := ((Identity.Pair.Spec).1 hzt).2
      exact htz.symm.trans htx
    · -- (→) Build `G` directly from `LeftInverseRelation`; no AC needed.
      intro hInj
      rcases hANon with ⟨a0, ha0A⟩
      let G : Set := LeftInverseRelation F B a0
      have hDomG : (dom G) = B := by
        apply extensionality
        intro u
        constructor
        · intro huDom
          rcases (Domain.Spec).1 huDom with ⟨v, huvG⟩
          rcases (LeftInverseRelation.Spec).1 huvG with hInv | hDef
          · have hvuF : ⟪v, u⟫ ∈ F := (Inverse.Pair.Spec).1 hInv
            exact hRanSub u (Relation.Pair.mem_ran F v u hvuF)
          · exact ((Difference.Spec).1 hDef.1).left
        · intro huB
          by_cases huRan : u ∈ ran F
          · rcases (Range.Spec).1 huRan with ⟨x, hxu⟩
            refine (Domain.Spec).2 ⟨x, ?_⟩
            exact (LeftInverseRelation.Spec).2 (Or.inl ((Inverse.Pair.Spec).2 hxu))
          · refine (Domain.Spec).2 ⟨a0, ?_⟩
            exact (LeftInverseRelation.Spec).2
              (Or.inr ⟨(Difference.Spec).2 ⟨huB, huRan⟩, rfl⟩)
      -- `G` is a function because `F` is one-to-one: every `b ∈ ran F`
      -- has a unique preimage, and every `b ∈ B - ran F` is paired with
      -- `a₀` only.
      have hGfun : IsFunction G := by
        refine ⟨?_, ?_⟩
        · intro w hw
          change w ∈ LeftInverseRelation F B a0 at hw
          rw [LeftInverseRelation, Union.Spec] at hw
          cases hw with
          | inl hInv =>
            rcases (Inverse.Spec).1 hInv with ⟨u, v, _, hEq⟩
            exact ⟨v, u, hEq⟩
          | inr hDef =>
            rcases (Product.Spec).1 hDef with ⟨x, y, _, _, hEq⟩
            exact ⟨x, y, hEq⟩
        · intro b hbDom
          rcases (Domain.Spec).1 hbDom with ⟨v, hbvG⟩
          refine ⟨v, hbvG, ?_⟩
          intro v' hbv'G
          rcases (LeftInverseRelation.Spec).1 hbvG with hInv | hDef
          · -- `b ∈ ran F`: `v = F⁻¹(b)`, and by single-rootedness so is `v'`.
            have hvbF : ⟪v, b⟫ ∈ F := (Inverse.Pair.Spec).1 hInv
            have hbRan : b ∈ ran F := Relation.Pair.mem_ran F v b hvbF
            rcases (LeftInverseRelation.Spec).1 hbv'G with hInv' | hDef'
            · have hv'bF : ⟪v', b⟫ ∈ F := (Inverse.Pair.Spec).1 hInv'
              exact (one_to_one_preimage_unique F v v' b hInj hvbF hv'bF).symm
            · exact absurd hbRan ((Difference.Spec).1 hDef'.1).right
          · -- `b ∈ B - ran F`: both `v` and `v'` must equal `a₀`.
            have hbNotRan : b ∉ ran F := ((Difference.Spec).1 hDef.1).right
            rcases (LeftInverseRelation.Spec).1 hbv'G with hInv' | hDef'
            · have hv'bF : ⟪v', b⟫ ∈ F := (Inverse.Pair.Spec).1 hInv'
              exact absurd (Relation.Pair.mem_ran F v' b hv'bF) hbNotRan
            · exact hDef'.2.trans hDef.2.symm
      have hRanGSubA : (ran G) ⊆ A := by
        intro v hvRan
        rcases (Range.Spec).1 hvRan with ⟨u, huvG⟩
        rcases (LeftInverseRelation.Spec).1 huvG with hInv | hDef
        · have hvuF : ⟪v, u⟫ ∈ F := (Inverse.Pair.Spec).1 hInv
          simpa [hDomF] using Relation.Pair.mem_dom F v u hvuF
        · simpa [hDef.2] using ha0A
      refine ⟨G, ⟨hGfun, hDomG, hRanGSubA⟩, ?_⟩
      apply extensionality
      intro w
      constructor
      · intro hwComp
        rcases (Composition.Spec).1 hwComp with ⟨_, x, z, t, hxtF, htzG, hEqw⟩
        have htRan : t ∈ ran F := Relation.Pair.mem_ran F x t hxtF
        have hztF : ⟪z, t⟫ ∈ F := by
          rcases (LeftInverseRelation.Spec).1 htzG with hInv | hDef
          · exact (Inverse.Pair.Spec).1 hInv
          · exact absurd htRan ((Difference.Spec).1 hDef.1).right
        have hxz : x = z := one_to_one_preimage_unique F x z t hInj hxtF hztF
        have hxA : x ∈ A := by
          simpa [hDomF] using Relation.Pair.mem_dom F x t hxtF
        subst hEqw
        exact (Identity.Pair.Spec).2 ⟨hxA, hxz.symm⟩
      · intro hwId
        rcases (Identity.Spec).1 hwId with ⟨_, x, hxA, hEqw⟩
        have hxDomF : x ∈ dom F := by simpa [hDomF] using hxA
        rcases hFfun.2 x hxDomF with ⟨y, hxyF, _⟩
        have hyRan : y ∈ ran F := Relation.Pair.mem_ran F x y hxyF
        have hyDomG : y ∈ dom G := by
          simpa [hDomG] using hRanSub y hyRan
        rcases hGfun.2 y hyDomG with ⟨z, hyzG, _⟩
        have hzyF : ⟪z, y⟫ ∈ F := by
          rcases (LeftInverseRelation.Spec).1 hyzG with hInv | hDef
          · exact (Inverse.Pair.Spec).1 hInv
          · exact absurd hyRan ((Difference.Spec).1 hDef.1).right
        have hzx : z = x := one_to_one_preimage_unique F z x y hInj hzyF hxyF
        have hyxG : ⟪y, x⟫ ∈ G := by simpa [hzx] using hyzG
        subst hEqw
        exact (Composition.Pair.Spec).2 ⟨y, hxyF, hyxG⟩

  /-
  Only the (→) direction of Theorem 3J(b) actually uses the Axiom of
  Choice — see the `choice_first_form` call below. We therefore put 3J(b)
  (and only 3J(b)) inside a reopened `Choice` namespace. The rest of
  §Functions — including 3J(a) and the `LeftInverseRelation` helper above
  — sits in the plain `Set` namespace and is AC-free.
  -/
  namespace Choice

  /-
  [Enderton, Theorem 3J(b), p. 48-49]
  For `F : A → B` with `A` nonempty, there is a right inverse `H : B → A`
  with `F ∘ H = I_B` iff `F` maps `A` onto `B`. The (→) direction is the
  textbook's first appeal to AC: take `R = F⁻¹` (a relation with
  `dom F⁻¹ = ran F = B`) and choose `H ⊆ R` via the first-form axiom.
  -/
  theorem thm_3J_b_right_inverse_iff_onto
      (F A B : Set) (hMap : MapsInto F A B) (_ : A.Nonempty) :
      (∃ H, MapsInto H B A ∧ (F ∘ H) = Identity B) ↔ MapsOnto F A B := by
    rcases hMap with ⟨hFfun, hDomF, hRanSub⟩
    constructor
    · -- (←) Any right inverse forces `ran F = B`. AC-free.
      rintro ⟨H, ⟨hHfun, hDomH, hRanHSubA⟩, hComp⟩
      refine ⟨⟨hFfun, hDomF, hRanSub⟩, ?_⟩
      apply extensionality
      intro b
      refine ⟨fun hbRan => hRanSub b hbRan, ?_⟩
      intro hbB
      have hbDomH : b ∈ dom H := by simpa [hDomH] using hbB
      rcases hHfun.2 b hbDomH with ⟨a, hbaH, _⟩
      have haA : a ∈ A := hRanHSubA a (Relation.Pair.mem_ran H b a hbaH)
      have haDomF : a ∈ dom F := by simpa [hDomF] using haA
      rcases hFfun.2 a haDomF with ⟨z, hazF, _⟩
      have hbzId : ⟪b, z⟫ ∈ Identity B := by
        have : ⟪b, z⟫ ∈ F ∘ H := (Composition.Pair.Spec).2 ⟨a, hbaH, hazF⟩
        simpa [hComp] using this
      have hzb : z = b := ((Identity.Pair.Spec).1 hbzId).2
      exact (Range.Spec).2 ⟨a, by simpa [hzb] using hazF⟩
    · -- (→) Choose `H ⊆ F⁻¹` via AC; this is the textbook's first appeal to AC.
      rintro ⟨_, hRanEqB⟩
      let R : Set := F⁻¹
      have hRRel : IsRelation R := by
        intro w hw
        rcases (Inverse.Spec).1 hw with ⟨u, v, _, hEq⟩
        exact ⟨v, u, hEq⟩
      -- *** Axiom of Choice (first form) used here. ***
      rcases choice_first_form R hRRel with ⟨H, hHSubR, hHfun, hDomHEqR⟩
      have hDomH : (dom H) = B :=
        hDomHEqR.trans ((thm_3E_domain_inverse F).trans hRanEqB)
      have hRanHSubA : (ran H) ⊆ A := by
        intro a haRan
        rcases (Range.Spec).1 haRan with ⟨b, hbaH⟩
        have habF : ⟪a, b⟫ ∈ F := (Inverse.Pair.Spec).1 (hHSubR _ hbaH)
        simpa [hDomF] using Relation.Pair.mem_dom F a b habF
      refine ⟨H, ⟨hHfun, hDomH, hRanHSubA⟩, ?_⟩
      apply extensionality
      intro w
      constructor
      · intro hwComp
        rcases (Composition.Spec).1 hwComp with ⟨_, b, z, a, hbaH, hazF, hEqw⟩
        have habF : ⟪a, b⟫ ∈ F := (Inverse.Pair.Spec).1 (hHSubR _ hbaH)
        have hzb : z = b := function_value_unique F a z b hFfun hazF habF
        have hbB : b ∈ B := by
          simpa [hDomH] using Relation.Pair.mem_dom H b a hbaH
        subst hEqw
        exact (Identity.Pair.Spec).2 ⟨hbB, hzb⟩
      · intro hwId
        rcases (Identity.Spec).1 hwId with ⟨_, b, hbB, hEqw⟩
        have hbDomH : b ∈ dom H := by simpa [hDomH] using hbB
        rcases hHfun.2 b hbDomH with ⟨a, hbaH, _⟩
        have habF : ⟪a, b⟫ ∈ F := (Inverse.Pair.Spec).1 (hHSubR _ hbaH)
        subst hEqw
        exact (Composition.Pair.Spec).2 ⟨a, hbaH, habF⟩

  end Choice
  -- #check thm_3J_b_right_inverse_iff_onto -- unidentifiable

  -- Invariant (kept as a build-time check):
  --   `Set.thm_3J_a_left_inverse_iff_one_to_one` must NOT depend on
  --   `Set.Choice.choice_first_form`, and
  --   `Set.Choice.thm_3J_b_right_inverse_iff_onto` MUST depend on it.
  -- Both depend on Lean's `Classical.choice` (metatheoretic), but that is
  -- separate from the set-theoretic Choice axiom we are tracking here.
  #print axioms thm_3J_a_left_inverse_iff_one_to_one
  #print axioms Choice.thm_3J_b_right_inverse_iff_onto

end Set
