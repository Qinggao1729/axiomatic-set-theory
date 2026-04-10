import Set.Choice

/-!
# Chapter 3, Section 5: Infinite Cartesian Products

Choice-related definitions and AC-dependent statements.
-/

namespace Set

#check ChoiceFirstForm
#check choice_first_form
#check ChoiceSecondForm

-- Infinite Cartesian product Π_{i∈I} H(i), represented via relation-valued H.
noncomputable def InfiniteProduct (I H : Set) : Set :=
  Comprehension
    (fun f =>
      IsFunction f ∧ (dom f) = I ∧
      ∀ i y, i ∈ I → ⟨i, y⟩ ∈ f → ∃ hi, ⟨i, hi⟩ ∈ H ∧ y ∈ hi)
    (𝒫 (I ⨯ ⋃ (ran H)))

lemma InfiniteProduct.Spec {I H f : Set} :
    f ∈ InfiniteProduct I H ↔
      f ∈ 𝒫 (I ⨯ ⋃ (ran H)) ∧
      IsFunction f ∧ (dom f) = I ∧
      (∀ i y, i ∈ I → ⟨i, y⟩ ∈ f → ∃ hi, ⟨i, hi⟩ ∈ H ∧ y ∈ hi) := by
  simp [InfiniteProduct, Comprehension.Spec]

lemma one_to_one_preimage_unique (F x z y : Set) :
    IsOneToOne F → ⟨x, y⟩ ∈ F → ⟨z, y⟩ ∈ F → x = z := by
  intro hInj hxy hzy
  rcases hInj with ⟨_, hSR⟩
  have hyRan : y ∈ ran F := Pair.mem_ran F x y hxy
  rcases hSR y hyRan with ⟨w, hw, huniq⟩
  have hxw : x = w := huniq x hxy
  have hzw : z = w := huniq z hzy
  exact hxw.trans hzw.symm

noncomputable def LeftInverseRelation (F B a0 : Set) : Set :=
  (Inverse F) ∪ (((B - ran F) ⨯ Singleton a0))

lemma LeftInverseRelation.Spec {F B a0 u v : Set} :
    ⟨u, v⟩ ∈ LeftInverseRelation F B a0 ↔
      (⟨u, v⟩ ∈ Inverse F ∨ (u ∈ (B - ran F) ∧ v = a0)) := by
  constructor
  · intro huv
    rw [LeftInverseRelation, Union.Spec] at huv
    cases huv with
    | inl hInv =>
      exact Or.inl hInv
    | inr hDef =>
      rcases (Product.Spec).1 hDef with
        ⟨x, y, hxDiff, hySing, hEq⟩
      rcases (OrderedPair.uniqueness u v x y).1 hEq with ⟨hux, hvy⟩
      subst hux
      have hvSing : v ∈ Singleton a0 := by simpa [hvy] using hySing
      exact Or.inr ⟨hxDiff, (Singleton.Spec).1 hvSing⟩
  · intro huv
    rw [LeftInverseRelation, Union.Spec]
    cases huv with
    | inl hInv =>
      exact Or.inl hInv
    | inr hDef =>
      rcases hDef with ⟨huDiff, hvEq⟩
      have hvSing : v ∈ Singleton a0 := by
        rw [Singleton.Spec]
        exact hvEq
      have hPair : OrderedPair u v ∈ ((B - ran F) ⨯ Singleton a0) :=
        Pair.mem_product (B - ran F) (Singleton a0) u v huDiff hvSing
      exact Or.inr hPair

-- Enderton Theorem 3J(a): left inverse iff one-to-one.
theorem left_inverse_iff_one_to_one
  (F A B : Set) :
  MapsInto F A B → A.Nonempty →
  ((∃ G, MapsInto G B A ∧ (Composition G F) = Identity A) ↔ IsOneToOne F)
  := by
  intro hMap hANon
  rcases hMap with ⟨hFfun, hDomF, hRanSub⟩
  constructor
  · intro hLeft
    rcases hLeft with ⟨G, hGMap, hComp⟩
    rcases hGMap with ⟨hGfun, hDomG, _⟩
    refine ⟨hFfun, ?_⟩
    intro y hyRan
    rcases (Relation.Range.Spec).1 hyRan with ⟨x, hxy⟩
    refine ⟨x, hxy, ?_⟩
    intro z hzy
    have hyB : y ∈ B := hRanSub y hyRan
    have hyDomG : y ∈ dom G := by simpa [hDomG] using hyB
    rcases hGfun.2 y hyDomG with ⟨t, hyt, _⟩
    have hxtComp : ⟨x, t⟩ ∈ Composition G F :=
      (Composition.Pair.Spec).2 ⟨y, hxy, hyt⟩
    have hztComp : ⟨z, t⟩ ∈ Composition G F :=
      (Composition.Pair.Spec).2 ⟨y, hzy, hyt⟩
    have hxtId : ⟨x, t⟩ ∈ Identity A := by simpa [hComp] using hxtComp
    have hztId : ⟨z, t⟩ ∈ Identity A := by simpa [hComp] using hztComp
    have htx : t = x := (Identity.Pair.Spec).1 hxtId |>.right
    have htz : t = z := (Identity.Pair.Spec).1 hztId |>.right
    exact (htx.symm.trans htz).symm
  · intro hInj
    rcases hANon with ⟨a0, ha0A⟩
    let R : Set := LeftInverseRelation F B a0
    have hInvRel : IsRelation (Inverse F) := by
      intro w hw
      rcases (Inverse.Spec).1 hw with ⟨u, v, _, hEq⟩
      exact ⟨v, u, hEq⟩
    have hRRel : IsRelation R := by
      intro w hw
      change w ∈ LeftInverseRelation F B a0 at hw
      rw [LeftInverseRelation, Union.Spec] at hw
      cases hw with
      | inl hInv =>
        exact hInvRel w hInv
      | inr hDef =>
        rcases (Product.Spec).1 hDef with ⟨x, y, _, _, hEq⟩
        exact ⟨x, y, hEq⟩
    rcases choice_first_form R hRRel with ⟨G, hGSubR, hGfun, hDomGEqR⟩
    have hDomR : (dom R) = B := by
      apply extensionality
      intro u
      constructor
      · intro huDom
        rcases (Relation.Domain.Spec).1 huDom with ⟨v, huvR⟩
        rcases (LeftInverseRelation.Spec).1 huvR with hInv | hDef
        · have hvuF : ⟨v, u⟩ ∈ F := (Inverse.Pair.Spec).1 hInv
          exact hRanSub u (Pair.mem_ran F v u hvuF)
        · exact (Difference.Spec).1 hDef.1 |>.left
      · intro huB
        by_cases huRan : u ∈ ran F
        · rcases (Relation.Range.Spec).1 huRan with ⟨x, hxu⟩
          have huvR : ⟨u, x⟩ ∈ R := by
            exact (LeftInverseRelation.Spec).2 (Or.inl ((Inverse.Pair.Spec).2 hxu))
          exact (Relation.Domain.Spec).2 ⟨x, huvR⟩
        · have huDiff : u ∈ B - ran F := (Difference.Spec).2 ⟨huB, huRan⟩
          have huuR : ⟨u, a0⟩ ∈ R := by
            exact (LeftInverseRelation.Spec).2
              (Or.inr ⟨huDiff, rfl⟩)
          exact (Relation.Domain.Spec).2 ⟨a0, huuR⟩
    have hDomG : (dom G) = B := by
      calc
        (dom G) = (dom R) := hDomGEqR
        _ = B := hDomR
    have hRanGSubA : (ran G) ⊆ A := by
      intro v hvRan
      rcases (Relation.Range.Spec).1 hvRan with ⟨u, huvG⟩
      have huvR : ⟨u, v⟩ ∈ R := hGSubR _ huvG
      rcases (LeftInverseRelation.Spec).1 huvR with hInv | hDef
      · have hvuF : ⟨v, u⟩ ∈ F := (Inverse.Pair.Spec).1 hInv
        have hvDomF : v ∈ dom F := Pair.mem_dom F v u hvuF
        simpa [hDomF] using hvDomF
      · rcases hDef with ⟨_, hvEq⟩
        simpa [hvEq] using ha0A
    have hGMap : MapsInto G B A := ⟨hGfun, hDomG, hRanGSubA⟩
    have hComp : Composition G F = Identity A := by
      apply extensionality
      intro w
      constructor
      · intro hwComp
        rcases (Composition.Spec).1 hwComp with ⟨_, x, z, t, hxtF, htzG, hEqw⟩
        have htzR : ⟨t, z⟩ ∈ R := hGSubR _ htzG
        have htRan : t ∈ ran F := Pair.mem_ran F x t hxtF
        have hztF : ⟨z, t⟩ ∈ F := by
          rcases (LeftInverseRelation.Spec).1 htzR with hInv | hDef
          · exact (Inverse.Pair.Spec).1 hInv
          · exfalso
            exact ((Difference.Spec).1 hDef.1 |>.right) htRan
        have hxz : x = z := one_to_one_preimage_unique F x z t hInj hxtF hztF
        have hxA : x ∈ A := by
          have hxDom : x ∈ dom F := Pair.mem_dom F x t hxtF
          simpa [hDomF] using hxDom
        subst hEqw
        exact (Identity.Pair.Spec).2 ⟨hxA, hxz.symm⟩
      · intro hwId
        rcases (Identity.Spec).1 hwId with ⟨_, x, hxA, hEqw⟩
        have hxDomF : x ∈ dom F := by simpa [hDomF] using hxA
        rcases hFfun.2 x hxDomF with ⟨y, hxyF, _⟩
        have hyRan : y ∈ ran F := Pair.mem_ran F x y hxyF
        have hyB : y ∈ B := hRanSub y hyRan
        have hyDomG : y ∈ dom G := by simpa [hDomG] using hyB
        rcases hGfun.2 y hyDomG with ⟨z, hyzG, _⟩
        have hyzR : ⟨y, z⟩ ∈ R := hGSubR _ hyzG
        have hzyF : ⟨z, y⟩ ∈ F := by
          rcases (LeftInverseRelation.Spec).1 hyzR with hInv | hDef
          · exact (Inverse.Pair.Spec).1 hInv
          · exfalso
            exact ((Difference.Spec).1 hDef.1 |>.right) hyRan
        have hzx : z = x := one_to_one_preimage_unique F z x y hInj hzyF hxyF
        have hyxG : ⟨y, x⟩ ∈ G := by simpa [hzx] using hyzG
        subst hEqw
        exact (Composition.Pair.Spec).2 ⟨y, hxyF, hyxG⟩
    exact ⟨G, hGMap, hComp⟩

-- Enderton Theorem 3J(b): right inverse iff onto (AC-dependent).
theorem right_inverse_iff_onto
  (F A B : Set) :
  MapsInto F A B → A.Nonempty →
  ((∃ H, MapsInto H B A ∧ (Composition F H) = Identity B) ↔ MapsOnto F A B)
  := by
  intro hMap _
  rcases hMap with ⟨hFfun, hDomF, hRanSub⟩
  constructor
  · intro hRight
    rcases hRight with ⟨H, hHMap, hComp⟩
    rcases hHMap with ⟨hHfun, hDomH, hRanHSubA⟩
    refine ⟨⟨hFfun, hDomF, hRanSub⟩, ?_⟩
    apply extensionality
    intro b
    constructor
    · intro hbRan
      exact hRanSub b hbRan
    · intro hbB
      have hbDomH : b ∈ dom H := by simpa [hDomH] using hbB
      rcases hHfun.2 b hbDomH with ⟨a, hbaH, _⟩
      have haA : a ∈ A := hRanHSubA a (Pair.mem_ran H b a hbaH)
      have haDomF : a ∈ dom F := by simpa [hDomF] using haA
      rcases hFfun.2 a haDomF with ⟨z, hazF, _⟩
      have hbzComp : ⟨b, z⟩ ∈ Composition F H :=
        (Composition.Pair.Spec).2 ⟨a, hbaH, hazF⟩
      have hbzId : ⟨b, z⟩ ∈ Identity B := by simpa [hComp] using hbzComp
      have hzb : z = b := (Identity.Pair.Spec).1 hbzId |>.right
      exact (Relation.Range.Spec).2 ⟨a, by simpa [hzb] using hazF⟩
  · intro hOnto
    rcases hOnto with ⟨_, hRanEqB⟩
    let R : Set := Inverse F
    have hRRel : IsRelation R := by
      intro w hw
      rcases (Inverse.Spec).1 hw with ⟨u, v, _, hEq⟩
      exact ⟨v, u, hEq⟩
    rcases choice_first_form R hRRel with ⟨H, hHSubR, hHfun, hDomHEqR⟩
    have hDomH : (dom H) = B := by
      calc
        (dom H) = (dom R) := hDomHEqR
        _ = ran F := domain_inverse F
        _ = B := hRanEqB
    have hRanHSubA : (ran H) ⊆ A := by
      intro a haRan
      rcases (Relation.Range.Spec).1 haRan with ⟨b, hbaH⟩
      have hbaR : ⟨b, a⟩ ∈ R := hHSubR _ hbaH
      have habF : ⟨a, b⟩ ∈ F := (Inverse.Pair.Spec).1 hbaR
      have haDomF : a ∈ dom F := Pair.mem_dom F a b habF
      simpa [hDomF] using haDomF
    have hHMap : MapsInto H B A := ⟨hHfun, hDomH, hRanHSubA⟩
    have hComp : Composition F H = Identity B := by
      apply extensionality
      intro w
      constructor
      · intro hwComp
        rcases (Composition.Spec).1 hwComp with ⟨_, b, z, a, hbaH, hazF, hEqw⟩
        have hbaR : ⟨b, a⟩ ∈ R := hHSubR _ hbaH
        have habF : ⟨a, b⟩ ∈ F := (Inverse.Pair.Spec).1 hbaR
        have hzb : z = b := function_value_unique F a z b hFfun hazF habF
        subst hEqw
        have hbB : b ∈ B := by
          have hbDomH : b ∈ dom H := Pair.mem_dom H b a hbaH
          simpa [hDomH] using hbDomH
        exact (Identity.Pair.Spec).2 ⟨hbB, hzb⟩
      · intro hwId
        rcases (Identity.Spec).1 hwId with ⟨_, b, hbB, hEqw⟩
        have hbDomH : b ∈ dom H := by simpa [hDomH] using hbB
        rcases hHfun.2 b hbDomH with ⟨a, hbaH, _⟩
        have hbaR : ⟨b, a⟩ ∈ R := hHSubR _ hbaH
        have habF : ⟨a, b⟩ ∈ F := (Inverse.Pair.Spec).1 hbaR
        subst hEqw
        exact (Composition.Pair.Spec).2 ⟨a, hbaH, habF⟩
    exact ⟨H, hHMap, hComp⟩ 

-- Enderton p.55: second-form AC yields nonempty infinite products.
theorem infiniteProduct_nonempty_of_choice_second_form
  (hChoice₂ : ChoiceSecondForm) :
  ∀ (I H : Set),
    IsFunction H →
    (dom H) = I →
    (∀ i, i ∈ I → ∃ hi, ⟨i, hi⟩ ∈ H ∧ hi.Nonempty) →
    (InfiniteProduct I H).Nonempty := by
  intro I H hHfun hDomH hFibers
  rcases hChoice₂ I H hHfun hDomH hFibers with ⟨f, hFfun, hDomF, hSel⟩
  have hPow : f ∈ 𝒫 (I ⨯ ⋃ (ran H)) := by
    rw [Power.Spec]
    intro w hwf
    rcases hFfun.1 w hwf with ⟨i, y, hEqw⟩
    have hiyf : ⟨i, y⟩ ∈ f := by simpa [hEqw] using hwf
    have hiDom : i ∈ dom f := Pair.mem_dom f i y hiyf
    have hiI : i ∈ I := by simpa [hDomF] using hiDom
    rcases hSel i y hiyf with ⟨hi, hihH, hyhi⟩
    have hhiRan : hi ∈ ran H := Pair.mem_ran H i hi hihH
    have hyBigUnion : y ∈ ⋃ (ran H) := (BigUnion.Spec).2 ⟨hi, hhiRan, hyhi⟩
    have hiyProd : ⟨i, y⟩ ∈ I ⨯ ⋃ (ran H) :=
      Pair.mem_product I (⋃ (ran H)) i y hiI hyBigUnion
    simpa [hEqw] using hiyProd
  have hfProd : f ∈ InfiniteProduct I H := (InfiniteProduct.Spec).2
    ⟨hPow, hFfun, hDomF, by
      intro i y hiI hiyf
      exact hSel i y hiyf⟩
  exact ⟨f, hfProd⟩

end Set
