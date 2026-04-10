import Set.Ch3.S4_Functions

/-!
# Chapter 3, Section 6: Equivalence Relations

Equivalence-relation constructions (3M/3N/3P and quotient API).
-/

namespace Set

def IsReflexiveOn (R A : Set) : Prop :=
  ∀ x, x ∈ A → ⟨x, x⟩ ∈ R

def IsSymmetric (R : Set) : Prop :=
  ∀ x y, ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R

def IsTransitiveRel (R : Set) : Prop :=
  ∀ x y z, ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R

def IsBinaryRelationOn (R A : Set) : Prop :=
  IsRelation R ∧ R ⊆ (A ⨯ A)

def IsEquivalenceRelation (R A : Set) : Prop :=
  IsBinaryRelationOn R A ∧ IsReflexiveOn R A ∧ IsSymmetric R ∧ IsTransitiveRel R

theorem symm_trans_is_equiv (R : Set) :
    IsRelation R → IsSymmetric R → IsTransitiveRel R → IsEquivalenceRelation R (fld R) := by
  intro hRel hSym hTrans
  refine ⟨?_, ?_, hSym, hTrans⟩
  · refine ⟨hRel, ?_⟩
    intro w hw
    rcases hRel w hw with ⟨x, y, rfl⟩
    apply Pair.mem_product (fld R) (fld R) x y
    · rw [Relation.Field.Spec, Relation.Domain.Spec]
      exact Or.inl ⟨y, hw⟩
    · rw [Relation.Field.Spec, Relation.Range.Spec]
      exact Or.inr ⟨x, hw⟩
  · intro x hxFld
    rw [Relation.Field.Spec] at hxFld
    cases hxFld with
    | inl hxDom =>
      rw [Relation.Domain.Spec] at hxDom
      rcases hxDom with ⟨y, hxy⟩
      have hyx : ⟨y, x⟩ ∈ R := hSym x y hxy
      exact hTrans x y x hxy hyx
    | inr hxRan =>
      rw [Relation.Range.Spec] at hxRan
      rcases hxRan with ⟨y, hyx⟩
      have hxy : ⟨x, y⟩ ∈ R := hSym y x hyx
      exact hTrans x y x hxy hyx

noncomputable def EquivalenceClass (x R : Set) : Set :=
  Comprehension (λ t ↦ ⟨x, t⟩ ∈ R) (ran R)

notation:90 "[" x "]₍" R "₎" => EquivalenceClass x R

lemma EquivalenceClass.Spec {x R t : Set} :
    t ∈ [x]₍R₎ ↔ t ∈ (ran R) ∧ ⟨x, t⟩ ∈ R := by
  simp [EquivalenceClass, Comprehension.Spec]

theorem equiv_class_eq_iff (R A x y : Set) :
    IsEquivalenceRelation R A → x ∈ A → y ∈ A →
    ([x]₍R₎ = [y]₍R₎ ↔ ⟨x, y⟩ ∈ R) := by
  intro hEq hxA hyA
  rcases hEq with ⟨⟨hRel, hBin⟩, hRefl, hSym, hTrans⟩
  apply Iff.intro
  · intro hClass
    have hyy : ⟨y, y⟩ ∈ R := hRefl y hyA
    have hyRan : y ∈ (ran R) := Pair.mem_ran R y y hyy
    have hyIn : y ∈ [y]₍R₎ := (EquivalenceClass.Spec).2 ⟨hyRan, hyy⟩
    have hyIn' : y ∈ [x]₍R₎ := by simpa [hClass] using hyIn
    exact (EquivalenceClass.Spec).1 hyIn' |>.right
  · intro hxy
    apply extensionality
    intro t
    apply Iff.intro
    · intro ht
      rcases (EquivalenceClass.Spec).1 ht with ⟨htRan, hxt⟩
      have hyx : ⟨y, x⟩ ∈ R := hSym x y hxy
      have hyt : ⟨y, t⟩ ∈ R := hTrans y x t hyx hxt
      exact (EquivalenceClass.Spec).2 ⟨htRan, hyt⟩
    · intro ht
      rcases (EquivalenceClass.Spec).1 ht with ⟨htRan, hyt⟩
      have hxt : ⟨x, t⟩ ∈ R := hTrans x y t hxy hyt
      exact (EquivalenceClass.Spec).2 ⟨htRan, hxt⟩

noncomputable def QuotientSet (A R : Set) : Set :=
  Comprehension
    (λ Q ↦ ∃ x, x ∈ A ∧ Q = [x]₍R₎)
    (𝒫 (ran R))

infixl:70 " / " => QuotientSet

lemma QuotientSet.Spec {A R Q : Set} :
    Q ∈ A / R ↔ Q ∈ 𝒫 (ran R) ∧ ∃ x, x ∈ A ∧ Q = [x]₍R₎ := by
  simp [QuotientSet, Comprehension.Spec]

def IsCompatible (F R A : Set) : Prop :=
  MapsInto F A A ∧
  ∀ x y u v, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨x, u⟩ ∈ F → ⟨y, v⟩ ∈ F → ⟨u, v⟩ ∈ R

lemma compatible_map_eqclass (R A F x y u v : Set) :
    IsEquivalenceRelation R A → IsCompatible F R A →
    x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨x, u⟩ ∈ F → ⟨y, v⟩ ∈ F →
    [u]₍R₎ = [v]₍R₎ := by
  intro hEqRel hCompat hxA hyA hxyR hxuF hyvF
  rcases hCompat with ⟨hMap, hCompatRel⟩
  rcases hMap with ⟨_, _, hRanSubA⟩
  have huA : u ∈ A := hRanSubA u (Pair.mem_ran F x u hxuF)
  have hvA : v ∈ A := hRanSubA v (Pair.mem_ran F y v hyvF)
  have huvR : ⟨u, v⟩ ∈ R := hCompatRel x y u v hxA hyA hxyR hxuF hyvF
  exact (equiv_class_eq_iff R A u v hEqRel huA hvA).2 huvR

-- Enderton Theorem 3Q (formalized statement).
lemma EquivalenceClass.mem_quotient (A R x : Set) :
    x ∈ A → [x]₍R₎ ∈ A / R := by
  intro hxA
  rw [QuotientSet.Spec]
  refine ⟨?_, x, hxA, rfl⟩
  rw [Power.Spec]
  intro t ht
  exact (EquivalenceClass.Spec).1 ht |>.left

noncomputable def QuotientLift (R A F : Set) : Set :=
  Comprehension
    (fun w => ∃ x y, x ∈ A ∧ ⟨x, y⟩ ∈ F ∧ w = ⟨[x]₍R₎, [y]₍R₎⟩)
    ((A / R) ⨯ (A / R))

lemma QuotientLift.Spec {R A F w : Set} :
    w ∈ QuotientLift R A F ↔
      w ∈ ((A / R) ⨯ (A / R)) ∧
      ∃ x y, x ∈ A ∧ ⟨x, y⟩ ∈ F ∧ w = ⟨[x]₍R₎, [y]₍R₎⟩ := by
  simp [QuotientLift, Comprehension.Spec]

lemma QuotientLift.Pair.Spec {R A F Q P : Set} :
    ⟨Q, P⟩ ∈ QuotientLift R A F ↔
      ⟨Q, P⟩ ∈ ((A / R) ⨯ (A / R)) ∧
      ∃ x y, x ∈ A ∧ ⟨x, y⟩ ∈ F ∧ Q = [x]₍R₎ ∧ P = [y]₍R₎ := by
  constructor
  · intro hQP
    rcases (QuotientLift.Spec).1 hQP with
      ⟨hProd, x, y, hxA, hxyF, hEq⟩
    rcases (OrderedPair.uniqueness Q P ([x]₍R₎) ([y]₍R₎)).1 hEq with ⟨hQ, hP⟩
    exact ⟨hProd, x, y, hxA, hxyF, hQ, hP⟩
  · intro hQP
    rcases hQP with ⟨hProd, x, y, hxA, hxyF, hQ, hP⟩
    exact (QuotientLift.Spec).2
      ⟨hProd, x, y, hxA, hxyF, by simp [hQ, hP]⟩

lemma QuotientLift.pair_intro (R A F x y : Set) (hMap : MapsInto F A A) :
    x ∈ A → ⟨x, y⟩ ∈ F → ⟨[x]₍R₎, [y]₍R₎⟩ ∈ QuotientLift R A F := by
  intro hxA hxyF
  rcases hMap with ⟨_, _, hRanSubA⟩
  have hyA : y ∈ A := hRanSubA y (Pair.mem_ran F x y hxyF)
  have hxQ : [x]₍R₎ ∈ A / R := EquivalenceClass.mem_quotient A R x hxA
  have hyQ : [y]₍R₎ ∈ A / R := EquivalenceClass.mem_quotient A R y hyA
  have hProd : ⟨[x]₍R₎, [y]₍R₎⟩ ∈ ((A / R) ⨯ (A / R)) :=
    Pair.mem_product (A / R) (A / R) ([x]₍R₎) ([y]₍R₎) hxQ hyQ
  exact (QuotientLift.Pair.Spec).2
    ⟨hProd, x, y, hxA, hxyF, rfl, rfl⟩

lemma QuotientLift.value_unique (R A F Q P₁ P₂ : Set)
    (hEqRel : IsEquivalenceRelation R A)
    (hCompat : IsCompatible F R A) :
    ⟨Q, P₁⟩ ∈ QuotientLift R A F →
    ⟨Q, P₂⟩ ∈ QuotientLift R A F →
    P₁ = P₂ := by
  intro hQP1 hQP2
  rcases (QuotientLift.Pair.Spec).1 hQP1 with
    ⟨_, x₁, y₁, hx₁A, hx₁y₁F, hQx₁, hP₁y₁⟩
  rcases (QuotientLift.Pair.Spec).1 hQP2 with
    ⟨_, x₂, y₂, hx₂A, hx₂y₂F, hQx₂, hP₂y₂⟩
  have hClassX : EquivalenceClass x₁ R = EquivalenceClass x₂ R := by
    calc
      EquivalenceClass x₁ R = Q := hQx₁.symm
      _ = EquivalenceClass x₂ R := hQx₂
  have hx₁x₂ : ⟨x₁, x₂⟩ ∈ R := (equiv_class_eq_iff R A x₁ x₂ hEqRel hx₁A hx₂A).1 hClassX
  have hClassY : EquivalenceClass y₁ R = EquivalenceClass y₂ R :=
    compatible_map_eqclass R A F x₁ x₂ y₁ y₂ hEqRel
      hCompat hx₁A hx₂A hx₁x₂ hx₁y₁F hx₂y₂F
  calc
    P₁ = EquivalenceClass y₁ R := hP₁y₁
    _ = EquivalenceClass y₂ R := hClassY
    _ = P₂ := hP₂y₂.symm

theorem quotient_function_exists
  (R A F : Set) :
  IsEquivalenceRelation R A → IsCompatible F R A →
  ∃! Fq, MapsInto Fq (A / R) (A / R) ∧
    (∀ x y, x ∈ A → ⟨x, y⟩ ∈ F → ⟨[x]₍R₎, [y]₍R₎⟩ ∈ Fq) := by
  intro hEqRel hCompatAll
  have hCompatKeep : IsCompatible F R A := hCompatAll
  rcases hCompatAll with ⟨hMap, _⟩
  rcases hMap with ⟨hFfun, hDomF, hRanSubA⟩
  let Fq : Set := QuotientLift R A F
  have hFqFun : IsFunction Fq := by
    refine ⟨?_, ?_⟩
    · intro w hw
      rcases (QuotientLift.Spec).1 hw with ⟨_, x, y, _, _, hEq⟩
      exact ⟨[x]₍R₎, [y]₍R₎, hEq⟩
    · intro Q hQDom
      rcases (Relation.Domain.Spec).1 hQDom with ⟨P₀, hQP₀⟩
      refine ⟨P₀, hQP₀, ?_⟩
      intro P hQP
      exact QuotientLift.value_unique R A F Q P P₀ hEqRel hCompatKeep hQP hQP₀
  have hDomFq : (dom Fq) = A / R := by
    apply extensionality
    intro Q
    constructor
    · intro hQDom
      rcases (Relation.Domain.Spec).1 hQDom with ⟨P, hQP⟩
      have hProd : ⟨Q, P⟩ ∈ ((A / R) ⨯ (A / R)) :=
        (QuotientLift.Pair.Spec).1 hQP |>.left
      rcases (Product.Spec).1 hProd with
        ⟨q, p, hqQ, _, hEq⟩
      have hqq : q = Q := (OrderedPair.uniqueness q p Q P).1 hEq.symm |>.left
      simpa [hqq] using hqQ
    · intro hQ
      rcases (QuotientSet.Spec).1 hQ with ⟨_, x, hxA, hQx⟩
      have hxDomF : x ∈ dom F := by simpa [hDomF] using hxA
      rcases hFfun.2 x hxDomF with ⟨y, hxyF, _⟩
      have hQPair : ⟨Q, [y]₍R₎⟩ ∈ Fq := by
        simpa [hQx] using (QuotientLift.pair_intro R A F x y ⟨hFfun, hDomF, hRanSubA⟩ hxA hxyF)
      exact (Relation.Domain.Spec).2 ⟨[y]₍R₎, hQPair⟩
  have hRanFqSub : (ran Fq) ⊆ A / R := by
    intro P hPRan
    rcases (Relation.Range.Spec).1 hPRan with ⟨Q, hQP⟩
    have hProd : ⟨Q, P⟩ ∈ ((A / R) ⨯ (A / R)) :=
      (QuotientLift.Pair.Spec).1 hQP |>.left
    rcases (Product.Spec).1 hProd with
      ⟨q, p, _, hpP, hEq⟩
    have hpp : p = P := (OrderedPair.uniqueness q p Q P).1 hEq.symm |>.right
    simpa [hpp] using hpP
  have hMaps : MapsInto Fq (A / R) (A / R) := ⟨hFqFun, hDomFq, hRanFqSub⟩
  have hSpec : ∀ x y, x ∈ A → ⟨x, y⟩ ∈ F → ⟨[x]₍R₎, [y]₍R₎⟩ ∈ Fq := by
    intro x y hxA hxyF
    exact QuotientLift.pair_intro R A F x y ⟨hFfun, hDomF, hRanSubA⟩ hxA hxyF
  refine ⟨Fq, ⟨hMaps, hSpec⟩, ?_⟩
  intro G hG
  rcases hG with ⟨hGMap, hGSpec⟩
  apply extensionality
  intro w
  constructor
  · intro hwG
    rcases hGMap.1.1 w hwG with ⟨Q, P, hEqw⟩
    subst hEqw
    have hQDomG : Q ∈ dom G := Pair.mem_dom G Q P hwG
    have hQQuot : Q ∈ A / R := by simpa [hGMap.2.1] using hQDomG
    rcases (QuotientSet.Spec).1 hQQuot with ⟨_, x, hxA, hQx⟩
    have hxDomF : x ∈ dom F := by simpa [hDomF] using hxA
    rcases hFfun.2 x hxDomF with ⟨y, hxyF, _⟩
    have hQyG : ⟨Q, [y]₍R₎⟩ ∈ G := by
      simpa [hQx] using hGSpec x y hxA hxyF
    have hPClass : P = [y]₍R₎ :=
      function_value_unique G Q P ([y]₍R₎) hGMap.1 hwG hQyG
    have hQyFq : ⟨Q, [y]₍R₎⟩ ∈ Fq := by
      simpa [hQx] using hSpec x y hxA hxyF
    simpa [hPClass] using hQyFq
  · intro hwFq
    rcases hFqFun.1 w hwFq with ⟨Q, P, hEqw⟩
    subst hEqw
    rcases (QuotientLift.Pair.Spec).1 hwFq with
      ⟨_, x, y, hxA, hxyF, hQx, hPy⟩
    have hQyG : ⟨[x]₍R₎, [y]₍R₎⟩ ∈ G := hGSpec x y hxA hxyF
    simpa [hQx, hPy] using hQyG

theorem quotient_function_not_exists
  (R A F : Set) :
  IsEquivalenceRelation R A → MapsInto F A A → ¬ IsCompatible F R A →
  ¬ ∃ Fq, MapsInto Fq (A / R) (A / R) ∧
    (∀ x y, x ∈ A → ⟨x, y⟩ ∈ F → ⟨[x]₍R₎, [y]₍R₎⟩ ∈ Fq) := by
  intro hEqRel hMap hNot hEx
  rcases hEx with ⟨Fq, hFqMap, hFqSpec⟩
  rcases hMap with ⟨hFfun, hDomF, hRanSubA⟩
  apply hNot
  refine ⟨⟨hFfun, hDomF, hRanSubA⟩, ?_⟩
  intro x y u v hxA hyA hxyR hxuF hyvF
  have hClassXY : [x]₍R₎ = [y]₍R₎ :=
    (equiv_class_eq_iff R A x y hEqRel hxA hyA).2 hxyR
  have hClassU : ⟨[x]₍R₎, [u]₍R₎⟩ ∈ Fq := hFqSpec x u hxA hxuF
  have hClassV : ⟨[y]₍R₎, [v]₍R₎⟩ ∈ Fq := hFqSpec y v hyA hyvF
  have hClassV' : ⟨[x]₍R₎, [v]₍R₎⟩ ∈ Fq := by
    simpa [hClassXY] using hClassV
  have hClassUV : [u]₍R₎ = [v]₍R₎ :=
    function_value_unique Fq ([x]₍R₎) ([u]₍R₎) ([v]₍R₎)
      hFqMap.1 hClassU hClassV'
  have huA : u ∈ A := hRanSubA u (Pair.mem_ran F x u hxuF)
  have hvA : v ∈ A := hRanSubA v (Pair.mem_ran F y v hyvF)
  exact (equiv_class_eq_iff R A u v hEqRel huA hvA).1 hClassUV

def IsPartition (Part A : Set) : Prop :=
  (∀ B, B ∈ Part → B.Nonempty ∧ B ⊆ A) ∧
  (∀ B C, B ∈ Part → C ∈ Part → (∃ x, x ∈ B ∧ x ∈ C) → B = C) ∧
  (∀ x, x ∈ A → ∃ B, B ∈ Part ∧ x ∈ B)

theorem equiv_classes_partition (R A : Set) :
    IsEquivalenceRelation R A → IsPartition (A / R) A := by
  intro hEq
  rcases hEq with ⟨⟨hRel, hBin⟩, hRefl, hSym, hTrans⟩
  have hEqRel : IsEquivalenceRelation R A := ⟨⟨hRel, hBin⟩, hRefl, hSym, hTrans⟩
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rcases (QuotientSet.Spec).1 hB with ⟨_, x, hxA, hBx⟩
    subst hBx
    refine ⟨?_, ?_⟩
    · have hxx : ⟨x, x⟩ ∈ R := hRefl x hxA
      have hxRan : x ∈ (ran R) := Pair.mem_ran R x x hxx
      exact ⟨x, (EquivalenceClass.Spec).2 ⟨hxRan, hxx⟩⟩
    · intro t ht
      have hxt : ⟨x, t⟩ ∈ R := (EquivalenceClass.Spec).1 ht |>.right
      have hPair : OrderedPair x t ∈ (A ⨯ A) := hBin (OrderedPair x t) hxt
      rw [Product.Spec] at hPair
      rcases hPair with ⟨x', y', hx'A, hy'A, hEqPair⟩
      have hxeq : x = x' ∧ t = y' := by
        simpa using (OrderedPair.uniqueness x t x' y').1 hEqPair
      aesop
  · intro B C hB hC hBC
    rcases (QuotientSet.Spec).1 hB with ⟨_, x, hxA, hBx⟩
    rcases (QuotientSet.Spec).1 hC with ⟨_, y, hyA, hCy⟩
    rcases hBC with ⟨t, htB, htC⟩
    have htB' : t ∈ EquivalenceClass x R := by simpa [hBx] using htB
    have htC' : t ∈ EquivalenceClass y R := by simpa [hCy] using htC
    have hxt : ⟨x, t⟩ ∈ R := (EquivalenceClass.Spec).1 htB' |>.right
    have hyt : ⟨y, t⟩ ∈ R := (EquivalenceClass.Spec).1 htC' |>.right
    have hty : ⟨t, y⟩ ∈ R := hSym y t hyt
    have hxy : ⟨x, y⟩ ∈ R := hTrans x t y hxt hty
    have hEqClass : EquivalenceClass x R = EquivalenceClass y R := (equiv_class_eq_iff R A x y hEqRel hxA hyA).2 hxy
    simpa [hBx, hCy] using hEqClass
  · intro x hxA
    refine ⟨EquivalenceClass x R, ?_, ?_⟩
    · rw [QuotientSet.Spec]
      refine ⟨?_, x, hxA, rfl⟩
      rw [Power.Spec]
      intro t ht
      exact (EquivalenceClass.Spec).1 ht |>.left
    · have hxx : ⟨x, x⟩ ∈ R := hRefl x hxA
      have hxRan : x ∈ (ran R) := Pair.mem_ran R x x hxx
      exact (EquivalenceClass.Spec).2 ⟨hxRan, hxx⟩

end Set
