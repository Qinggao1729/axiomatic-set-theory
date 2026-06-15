import Set.Ch3.S4_Functions
import Set.Ch3.S3_NAryRelations

/-!
# Chapter 3, Section 6: Equivalence Relations

Equivalence-relation constructions (3M/3N/3P and quotient API).
-/

namespace Set

/-- [Enderton Ch3 §6, p.56] "`R` is reflexive on `A`, by which we mean that
`xRx` for all `x ∈ A`." -/
def IsReflexiveOn (R A : Set) : Prop :=
  ∀ {x}, x ∈ A → ⟪x, x⟫ ∈ R

/-- [Enderton Ch3 §6, p.56] "`R` is symmetric, by which we mean that whenever
`xRy`, then also `yRx`." -/
def IsSymmetric (R : Set) : Prop :=
  ∀ {x y}, ⟪x, y⟫ ∈ R → ⟪y, x⟫ ∈ R

/-- [Enderton Ch3 §6, p.56] "`R` is transitive, by which we mean that whenever
`xRy` and `yRz`, then also `xRz`." -/
-- Name note: `IsTransitiveRel` distinguishes relation-transitivity
-- (`⟪x, y⟫ ∈ R`) from any future set-level/transitive-set predicate.
def IsTransitiveRel (R : Set) : Prop :=
  ∀ {x y z}, ⟪x, y⟫ ∈ R → ⟪y, z⟫ ∈ R → ⟪x, z⟫ ∈ R

/-- [Enderton Ch3 §6, p.56] "Definition: `R` is an equivalence relation on `A`
iff `R` is a binary relation on `A` that is reflexive on `A`, symmetric, and
transitive." -/
def IsEquivalenceRelation (R A : Set) : Prop :=
  IsBinaryRelationOn R A ∧ IsReflexiveOn R A ∧ IsSymmetric R ∧ IsTransitiveRel R

/-- [Enderton Ch3 §6, p.56] "Theorem 3M: If `R` is a symmetric and transitive
relation, then `R` is an equivalence relation on `fld R`." -/
theorem thm_3M_symm_trans_is_equiv (R : Set) :
    IsRelation R → IsSymmetric R → IsTransitiveRel R → IsEquivalenceRelation R (fld R) := by
  intro hRel hSym hTrans
  refine ⟨?_, ?_, hSym, hTrans⟩
  · refine ⟨hRel, ?_⟩
    intro w hw
    rcases hRel w hw with ⟨x, y, rfl⟩
    apply (Product.Pair.Spec).2
    constructor
    · rw [Field.Spec, Domain.Spec]
      exact Or.inl ⟨y, hw⟩
    · rw [Field.Spec, Range.Spec]
      exact Or.inr ⟨x, hw⟩
  · intro x hxFld
    rw [Field.Spec] at hxFld
    cases hxFld with
    | inl hxDom =>
      rw [Domain.Spec] at hxDom
      rcases hxDom with ⟨y, hxy⟩
      have hyx : ⟪y, x⟫ ∈ R := hSym hxy
      exact hTrans hxy hyx
    | inr hxRan =>
      rw [Range.Spec] at hxRan
      rcases hxRan with ⟨y, hyx⟩
      have hxy : ⟪x, y⟫ ∈ R := hSym hyx
      exact hTrans hxy hyx

/-- [Enderton Ch3 §6, p.57] "Definition: The set `[x]₍R₎` is defined by
`[x]₍R₎ = {t | xRt}`. If `R` is an equivalence relation and `x ∈ fld R`, then
`[x]₍R₎` is called the equivalence class of `x` (modulo `R`)."

Following the textbook, the *set* is defined for arbitrary `R` and `x`; only
the *name* "equivalence class" presupposes that `R` is an equivalence
relation. The theorems that need that hypothesis (3N/3P/3Q) state it
explicitly. (Implemented with carrier `ran R`.) -/
noncomputable def EquivalenceClass (x R : Set) : Set :=
  Comprehension (λ t ↦ ⟪x, t⟫ ∈ R) (ran R)

notation:90 "[" x "]₍" R "₎" => EquivalenceClass x R

@[simp]
lemma EquivalenceClass.Spec_full {x R t : Set} :
    t ∈ [x]₍R₎ ↔ t ∈ (ran R) ∧ ⟪x, t⟫ ∈ R := by
  simp [EquivalenceClass, Comprehension.Spec]

@[simp]
lemma EquivalenceClass.Spec {x R t : Set} :
    t ∈ [x]₍R₎ ↔ ⟪x, t⟫ ∈ R := by
  constructor
  · intro ht
    exact (EquivalenceClass.Spec_full).1 ht |>.2
  · intro hxt
    exact (EquivalenceClass.Spec_full).2 ⟨(Range.Spec).2 ⟨x, hxt⟩, hxt⟩
attribute [set_spec_simps] EquivalenceClass.Spec

/-- [Enderton Ch3 §6, p.57] "Lemma 3N: Assume that `R` is an equivalence
relation on `A` and that `x` and `y` belong to `A`. Then
`[x]₍R₎ = [y]₍R₎ ↔ xRy`." -/
theorem lem_3N_equiv_class_eq_iff {R A x y : Set}
    (hEq : IsEquivalenceRelation R A) (hxA : x ∈ A) (hyA : y ∈ A) :
    [x]₍R₎ = [y]₍R₎ ↔ ⟪x, y⟫ ∈ R := by
  rcases hEq with ⟨_, hRefl, hSym, hTrans⟩
  apply Iff.intro
  · intro hClass
    have hyy : ⟪y, y⟫ ∈ R := hRefl hyA
    have hyIn : y ∈ [y]₍R₎ := (EquivalenceClass.Spec).2 hyy
    have hyIn' : y ∈ [x]₍R₎ := by simpa [hClass] using hyIn
    exact (EquivalenceClass.Spec).1 hyIn'
  · intro hxy
    apply extensionality
    intro t
    apply Iff.intro
    · intro ht
      have hxt : ⟪x, t⟫ ∈ R := (EquivalenceClass.Spec).1 ht
      have hyx : ⟪y, x⟫ ∈ R := hSym hxy
      have hyt : ⟪y, t⟫ ∈ R := hTrans hyx hxt
      exact (EquivalenceClass.Spec).2 hyt
    · intro ht
      have hyt : ⟪y, t⟫ ∈ R := (EquivalenceClass.Spec).1 ht
      have hxt : ⟪x, t⟫ ∈ R := hTrans hxy hyt
      exact (EquivalenceClass.Spec).2 hxt

/-- [Enderton Ch3 §6, p.57] "Definition: A partition `Π` of a set `A` is a set
of nonempty subsets of `A` that is disjoint and exhaustive." -/
def IsPartition (Pi A : Set) : Prop :=
  (∀ B, B ∈ Pi → B.Nonempty ∧ B ⊆ A) ∧
  (∀ B C, B ∈ Pi → C ∈ Pi → (∃ x, x ∈ B ∧ x ∈ C) → B = C) ∧
  (∀ x, x ∈ A → ∃ B, B ∈ Pi ∧ x ∈ B)

/-- [Enderton Ch3 §6, p.58] "If `R` is an equivalence relation on `A`, then we
can define the quotient set `A / R = {[x]₍R₎ | x ∈ A}` whose members are the
equivalence classes. (The expression `A / R` is read 'A modulo R'.)"

Order note: Enderton names `A / R` only *after* Theorem 3P (his 3P statement
reads "the set `{[x]₍R₎ | x ∈ A}` of all equivalence classes"). We define it
just before 3P because the formal statement of 3P needs a name for this set —
it is literally the same comprehension.

Hypothesis note: unlike `[x]₍R₎` (which Enderton defines for arbitrary `R`),
the textbook introduces `A / R` only *under the hypothesis* that `R` is an
equivalence relation on `A`. We build that requirement into the definition as
a trailing explicit proof argument, written `A / R ∵ h` where
`h : IsEquivalenceRelation R A` (`∵` reads "because": the quotient exists
*because* `R` is an equivalence relation). No tactic discharge is involved:
the hypothesis is normally given by name in the context, so it is simply
passed. The `∵` marker keeps proofs visually distinct from set-valued
subscripts like `[x]₍R₎` and from the function-value `'(...)` symbol. By
proof irrelevance the resulting set does not depend on which proof is
passed. -/
noncomputable def QuotientSet (A R : Set)
    (_hEq : IsEquivalenceRelation R A) : Set :=
  Comprehension
    (λ Q ↦ ∃ x, x ∈ A ∧ Q = [x]₍R₎)
    (𝒫 (ran R))

/-- Textbook `A / R`, with the equivalence-relation evidence attached:
`A / R ∵ h` abbreviates `QuotientSet A R h`. -/
syntax:70 term:70 " / " term:71 " ∵ " term:max : term

macro_rules
  | `($A / $R ∵ $h) => `(QuotientSet $A $R $h)

/-- Pretty-print `QuotientSet A R h` back to `A / R ∵ h`. -/
@[app_unexpander QuotientSet]
def unexpandQuotientSet : Lean.PrettyPrinter.Unexpander
  | `($_ $A $R $h) => `($A / $R ∵ $h)
  | _ => throw ()

@[simp]
lemma QuotientSet.Spec_full {A R Q : Set} {hEq : IsEquivalenceRelation R A} :
    Q ∈ A / R ∵ hEq ↔ Q ∈ 𝒫 (ran R) ∧ ∃ x, x ∈ A ∧ Q = [x]₍R₎ := by
  simp [QuotientSet, Comprehension.Spec]

@[simp]
lemma QuotientSet.Spec {A R Q : Set} {hEq : IsEquivalenceRelation R A} :
    Q ∈ A / R ∵ hEq ↔ ∃ x, x ∈ A ∧ Q = [x]₍R₎ := by
  constructor
  · intro hQ
    exact (QuotientSet.Spec_full).1 hQ |>.2
  · intro hQ
    rcases hQ with ⟨x, hxA, hQx⟩
    refine (QuotientSet.Spec_full).2 ⟨?_, x, hxA, hQx⟩
    subst hQx
    rw [Power.Spec]
    intro t ht
    exact (EquivalenceClass.Spec_full).1 ht |>.left
attribute [set_spec_simps] QuotientSet.Spec

/-- [Enderton Ch3 §6, pp.57–58] "Theorem 3P: Assume that `R` is an equivalence
relation on `A`. Then the set `{[x]₍R₎ | x ∈ A}` of all equivalence classes is
a partition of `A`." -/
theorem thm_3P_equiv_classes_partition (R A : Set)
    (hEq : IsEquivalenceRelation R A) :
    IsPartition (A / R ∵ hEq) A := by
  -- `hEq` cannot be destructed away (`rcases`/`obtain` would clear it, but
  -- the goal `A / R ∵ hEq` depends on it), so copy it and destructure the copy.
  have hEq' := hEq
  obtain ⟨⟨_, hBin⟩, hRefl, hSym, hTrans⟩ := hEq'
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rcases (QuotientSet.Spec).1 hB with ⟨x, hxA, hBx⟩
    subst hBx
    refine ⟨?_, ?_⟩
    · have hxx : ⟪x, x⟫ ∈ R := hRefl hxA
      exact ⟨x, (EquivalenceClass.Spec).2 hxx⟩
    · intro t ht
      -- Textbook: `[x]₍R₎ ⊆ A` "because `R` is a binary relation on `A`."
      have hxt : ⟪x, t⟫ ∈ R := (EquivalenceClass.Spec).1 ht
      exact ((Product.Pair.Spec).1 (hBin _ hxt)).2
  · intro B C hB hC hBC
    rcases (QuotientSet.Spec).1 hB with ⟨x, hxA, hBx⟩
    rcases (QuotientSet.Spec).1 hC with ⟨y, hyA, hCy⟩
    subst hBx
    subst hCy
    rcases hBC with ⟨t, htB, htC⟩
    have hxt : ⟪x, t⟫ ∈ R := (EquivalenceClass.Spec).1 htB
    have hyt : ⟪y, t⟫ ∈ R := (EquivalenceClass.Spec).1 htC
    have hty : ⟪t, y⟫ ∈ R := hSym hyt
    have hxy : ⟪x, y⟫ ∈ R := hTrans hxt hty
    exact (lem_3N_equiv_class_eq_iff hEq hxA hyA).2 hxy
  · intro x hxA
    refine ⟨[x]₍R₎, ?_, ?_⟩
    · exact (QuotientSet.Spec).2 ⟨x, hxA, rfl⟩
    · have hxx : ⟪x, x⟫ ∈ R := hRefl hxA
      exact (EquivalenceClass.Spec).2 hxx

/-- [Enderton Ch3 §6, p.58] (Continuing "If `R` is an equivalence relation on
`A`, then...") "We also have the natural map (or canonical map)
`φ : A → A / R` defined by `φ(x) = [x]₍R₎` for `x ∈ A`."

Like `QuotientSet`, the textbook introduces this only under the
equivalence-relation hypothesis, so the requirement is built into the
definition as a trailing explicit proof argument. -/
noncomputable def NaturalMap (A R : Set)
    (hEq : IsEquivalenceRelation R A) : Set :=
  Comprehension
    (fun w => ∃ x, x ∈ A ∧ w = ⟪x, [x]₍R₎⟫)
    (A ⨯ (A / R ∵ hEq))

@[simp]
lemma NaturalMap.Spec_full {A R w : Set} {hEq : IsEquivalenceRelation R A} :
    w ∈ NaturalMap A R hEq ↔
      w ∈ (A ⨯ (A / R ∵ hEq)) ∧ ∃ x, x ∈ A ∧ w = ⟪x, [x]₍R₎⟫ := by
  simp [NaturalMap, Comprehension.Spec]
@[simp]
lemma NaturalMap.Spec {A R w : Set} {hEq : IsEquivalenceRelation R A} :
    w ∈ NaturalMap A R hEq ↔ ∃ x, x ∈ A ∧ w = ⟪x, [x]₍R₎⟫ := by
  constructor
  · intro hw
    exact (NaturalMap.Spec_full).1 hw |>.2
  · intro hw
    rcases hw with ⟨x, hxA, hEq⟩
    refine (NaturalMap.Spec_full).2 ⟨?_, x, hxA, hEq⟩
    subst hEq
    exact (Product.Pair.Spec).2 ⟨hxA, (QuotientSet.Spec).2 ⟨x, hxA, rfl⟩⟩
attribute [set_spec_simps] NaturalMap.Spec

/-- [Enderton Ch3 §6, p.59] Specifically, assume that `R` is an equivalence relation on `A` and
that `F : A → A`. We ask whether or not there exists a corresponding function `F̂ : A / R → A / R`
such that for all `x ∈ A`, `F̂([x]₍R₎) = [F(x)]₍R₎`.
[Enderton Ch3 §6, p.60] "Let us say that `F` is compatible with `R` iff
for all `x` and `y` in `A`, `xRy ⇒ F(x)RF(y)`." -/
def IsCompatible (F R A : Set) : Prop :=
  ∃ _ : MapsInto F A A,
    ∀ (x y : Set) (hxA : x ∈ A) (hyA : y ∈ A),
      ⟪x, y⟫ ∈ R → ⟪F⟮x⟯, F⟮y⟯⟫ ∈ R

lemma mapsInto_of_isCompatible {F R A : Set} :
    IsCompatible F R A → MapsInto F A A := by
  intro hCompat
  rcases hCompat with ⟨hMap, _⟩
  exact hMap
-- Registered as a bridge for `F⟮x⟯` side conditions:
-- once this yields `MapsInto F A A`, `function_eval_auto` then uses
-- `isFunction_of_mapsInto` and `mapsInto_dom_mem` (from S4) to prove
-- `IsFunction F` and `x ∈ dom F`.
attribute [function_eval_sideconds] mapsInto_of_isCompatible
attribute [aesop safe forward] mapsInto_of_isCompatible

lemma compatible_preserves_equiv_class (R A F x y : Set)
    (hEqRel : IsEquivalenceRelation R A) (hCompat : IsCompatible F R A)
    (hxA : x ∈ A) (hyA : y ∈ A) (hxyR : ⟪x, y⟫ ∈ R) :
    [F⟮x⟯]₍R₎ = [F⟮y⟯]₍R₎ := by
  rcases hCompat with ⟨hMap, hCompatImp⟩
  have hFfun : IsFunction F := isFunction_of_mapsInto hMap
  have hxDomF : x ∈ dom F := mapsInto_dom_mem hMap hxA
  have hyDomF : y ∈ dom F := mapsInto_dom_mem hMap hyA
  have hFxA : F⟮x⟯ ∈ A := by
    exact hMap.2.2 _ (FunctionValue.mem_ran F x hFfun hxDomF)
  have hFyA : F⟮y⟯ ∈ A := by
    exact hMap.2.2 _ (FunctionValue.mem_ran F y hFfun hyDomF)
  exact (lem_3N_equiv_class_eq_iff hEqRel hFxA hFyA).2 (hCompatImp x y hxA hyA hxyR)

lemma equivalenceClass_mem_quotient (A R x : Set)
    (hEq : IsEquivalenceRelation R A) :
    x ∈ A → [x]₍R₎ ∈ A / R ∵ hEq := by
  intro hxA
  exact (QuotientSet.Spec).2 ⟨x, hxA, rfl⟩

/-- [Enderton Ch3 §6, pp.60–61] "Theorem 3Q: Assume that `R` is an
equivalence relation on `A` and that `F : A → A`. If `F` is compatible with
`R`, then there exists a unique `F̂ : A / R → A / R` such that for all
`x ∈ A`, `F̂([x]₍R₎) = [F(x)]₍R₎`." -/
noncomputable def QuotientLift (R A F : Set)
    (hEq : IsEquivalenceRelation R A) (hMap : MapsInto F A A) : Set :=
  Comprehension
    (fun w => ∃ x, ∃ hxA : x ∈ A, w = ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫)
    ((A / R ∵ hEq) ⨯ (A / R ∵ hEq))

@[simp]
lemma QuotientLift.Spec {R A F w : Set}
    {hEq : IsEquivalenceRelation R A} {hMap : MapsInto F A A} :
    w ∈ QuotientLift R A F hEq hMap ↔
      w ∈ ((A / R ∵ hEq) ⨯ (A / R ∵ hEq)) ∧
      ∃ x, ∃ hxA : x ∈ A, w = ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ := by
  simp [QuotientLift, Comprehension.Spec]
attribute [set_spec_simps] QuotientLift.Spec

@[simp]
lemma QuotientLift.Pair.Spec {R A F Q P : Set}
    {hEq : IsEquivalenceRelation R A} {hMap : MapsInto F A A} :
    ⟪Q, P⟫ ∈ QuotientLift R A F hEq hMap ↔
      ⟪Q, P⟫ ∈ ((A / R ∵ hEq) ⨯ (A / R ∵ hEq)) ∧
      ∃ x, ∃ hxA : x ∈ A, Q = [x]₍R₎ ∧ P = [F⟮x⟯]₍R₎ := by
  constructor
  · intro hQP
    rcases (QuotientLift.Spec).1 hQP with ⟨hProd, x, hxA, hEqPair⟩
    rcases (OrderedPair.uniqueness Q P ([x]₍R₎) ([F⟮x⟯]₍R₎)).1 hEqPair with ⟨hQ, hP⟩
    exact ⟨hProd, x, hxA, hQ, hP⟩
  · intro hQP
    rcases hQP with ⟨hProd, x, hxA, hQ, hP⟩
    exact (QuotientLift.Spec).2 ⟨hProd, x, hxA, by simp [hQ, hP]⟩
attribute [set_spec_simps] QuotientLift.Pair.Spec

lemma QuotientLift.pair_intro_app (R A F x : Set)
    (hEq : IsEquivalenceRelation R A) (hMap : MapsInto F A A)
    (hxA : x ∈ A) :
    ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ QuotientLift R A F hEq hMap := by
  have hxDomF : x ∈ dom F := by simpa [hMap.2.1] using hxA
  have hFxA : F⟮x⟯ ∈ A := hMap.2.2 _ (FunctionValue.mem_ran F x hMap.1 hxDomF)
  have hxQ : [x]₍R₎ ∈ A / R ∵ hEq := equivalenceClass_mem_quotient A R x hEq hxA
  have hFxQ : [F⟮x⟯]₍R₎ ∈ A / R ∵ hEq :=
    equivalenceClass_mem_quotient A R F⟮x⟯ hEq hFxA
  have hProd : ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ ((A / R ∵ hEq) ⨯ (A / R ∵ hEq)) :=
    (Product.Pair.Spec).2 ⟨hxQ, hFxQ⟩
  exact (QuotientLift.Pair.Spec).2 ⟨hProd, x, hxA, rfl, rfl⟩

lemma QuotientLift.value_unique (R A F Q P₁ P₂ : Set)
    (hEqRel : IsEquivalenceRelation R A)
    (hCompat : IsCompatible F R A) :
    ⟪Q, P₁⟫ ∈ QuotientLift R A F hEqRel (mapsInto_of_isCompatible hCompat) →
    ⟪Q, P₂⟫ ∈ QuotientLift R A F hEqRel (mapsInto_of_isCompatible hCompat) →
    P₁ = P₂ := by
  intro hQP1 hQP2
  rcases (QuotientLift.Pair.Spec).1 hQP1 with ⟨_, x₁, hx₁A, hQx₁, hP₁x₁⟩
  rcases (QuotientLift.Pair.Spec).1 hQP2 with ⟨_, x₂, hx₂A, hQx₂, hP₂x₂⟩
  subst hQx₁
  -- After substitution `hQx₂ : [x₁]₍R₎ = [x₂]₍R₎`, so `x₁ R x₂` by Lemma 3N.
  have hx₁x₂ : ⟪x₁, x₂⟫ ∈ R := (lem_3N_equiv_class_eq_iff hEqRel hx₁A hx₂A).1 hQx₂
  rcases hCompat with ⟨hMap, hCompatImp⟩
  have hFfun : IsFunction F := hMap.1
  have hx₁DomF : x₁ ∈ dom F := mapsInto_dom_mem hMap hx₁A
  have hx₂DomF : x₂ ∈ dom F := mapsInto_dom_mem hMap hx₂A
  have hFx₁A : F⟮x₁⟯ ∈ A := hMap.2.2 _ (FunctionValue.mem_ran F x₁ hFfun hx₁DomF)
  have hFx₂A : F⟮x₂⟯ ∈ A := hMap.2.2 _ (FunctionValue.mem_ran F x₂ hFfun hx₂DomF)
  have hFF : ⟪F⟮x₁⟯, F⟮x₂⟯⟫ ∈ R := hCompatImp x₁ x₂ hx₁A hx₂A hx₁x₂
  have hClassY : [F⟮x₁⟯]₍R₎ = [F⟮x₂⟯]₍R₎ :=
    (lem_3N_equiv_class_eq_iff hEqRel hFx₁A hFx₂A).2 hFF
  calc
    P₁ = [F⟮x₁⟯]₍R₎ := hP₁x₁
    _ = [F⟮x₂⟯]₍R₎ := hClassY
    _ = P₂ := hP₂x₂.symm

/-- [Enderton Ch3 §6, pp.60–61] "Theorem 3Q (first clause): Assume that `R` is an
equivalence relation on `A` and that `F : A → A`. If `F` is compatible with
`R`, then there exists a unique `F̂ : A / R → A / R` such that for all
`x ∈ A`, `F̂([x]₍R₎) = [F(x)]₍R₎`." -/
theorem thm_3Q_compatible_exists_unique_quotient_map
  (R A F : Set) (hEqRel : IsEquivalenceRelation R A)
  (hCompat : IsCompatible F R A) :
  ∃! Fq, MapsInto Fq (A / R ∵ hEqRel) (A / R ∵ hEqRel) ∧
    (∀ x (hxA : x ∈ A), ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ Fq) := by
  -- Step 1: extract the map hypothesis and define Enderton's candidate
  -- `F̂ = {⟨[x],[F(x)]⟩ | x ∈ A}`.
  have hMap : MapsInto F A A := mapsInto_of_isCompatible hCompat
  let Fq : Set := QuotientLift R A F hEqRel hMap

  -- Step 2: show this candidate `Fq` really is a function (is a relation and has unique values)
  have hFqFun : IsFunction Fq := by
    refine ⟨?_, ?_⟩
    · intro w hw
      rcases (QuotientLift.Spec).1 hw with ⟨_, x, _, hEq⟩
      exact ⟨[x]₍R₎, [F⟮x⟯]₍R₎, hEq⟩
    · intro Q hQDom
      rcases (Domain.Spec).1 hQDom with ⟨P₀, hQP₀⟩
      refine ⟨P₀, hQP₀, ?_⟩
      intro P hQP
      exact QuotientLift.value_unique R A F Q P P₀ hEqRel hCompat hQP hQP₀

  -- Step 3: verify `F̂ : A/R → A/R` (is a function (done), `dom F̂ = A/R`, `ran F̂ ⊆ A/R`.)
  have hDomFq : (dom Fq) = A / R ∵ hEqRel := by
    apply extensionality
    intro Q
    constructor
    · intro hQDom
      rcases (Domain.Spec).1 hQDom with ⟨P, hQP⟩
      have hProd : ⟪Q, P⟫ ∈ ((A / R ∵ hEqRel) ⨯ (A / R ∵ hEqRel)) :=
        (QuotientLift.Pair.Spec).1 hQP |>.left
      exact ((Product.Pair.Spec).1 hProd).left
    · intro hQ
      rcases (QuotientSet.Spec).1 hQ with ⟨x, hxA, hQx⟩
      have hQPair : ⟪Q, [F⟮x⟯]₍R₎⟫ ∈ Fq := by
        subst hQx
        exact QuotientLift.pair_intro_app R A F x hEqRel hMap hxA
      exact (Domain.Spec).2 ⟨[F⟮x⟯]₍R₎, hQPair⟩
  have hRanFqSub : (ran Fq) ⊆ A / R ∵ hEqRel := by
    intro P hPRan
    rcases (Range.Spec).1 hPRan with ⟨Q, hQP⟩
    have hProd : ⟪Q, P⟫ ∈ ((A / R ∵ hEqRel) ⨯ (A / R ∵ hEqRel)) :=
      (QuotientLift.Pair.Spec).1 hQP |>.left
    exact ((Product.Pair.Spec).1 hProd).right
  have hMaps : MapsInto Fq (A / R ∵ hEqRel) (A / R ∵ hEqRel) := ⟨hFqFun, hDomFq, hRanFqSub⟩

  -- Step 4: verify the defining graph condition
  -- `⟨[x]₍R₎, [F(x)]₍R₎⟩ ∈ F̂` for each `x ∈ A`.
  have hSpec : ∀ x (hxA : x ∈ A), ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ Fq := by
    intro x hxA
    simpa [Fq] using QuotientLift.pair_intro_app R A F x hEqRel hMap hxA

  -- Step 5: uniqueness — any `G` with the same graph condition equals `Fq`.
  -- Idea: both `G` and `Fq` are functions on `A / R` pinned by the same rule
  -- `[x]₍R₎ ↦ [F⟮x⟯]₍R₎`, so their graphs must coincide. We prove `G = Fq` by
  -- extensionality on pairs `⟪Q, P⟫` (⊆ and ⊇)
  refine ⟨Fq, ⟨hMaps, hSpec⟩, ?_⟩
  intro G hG
  rcases hG with ⟨hGMap, hGSpec⟩
  apply extensionality
  intro w
  constructor
  --  • (⊆) if `⟪Q, P⟫ ∈ G`, then `Q ∈ dom G = A / R`, so `Q = [x]₍R₎` for some
  --    `x ∈ A`; functionality of `G` together with its rule forces
  --    `P = [F⟮x⟯]₍R₎`, and the same rule for `Fq` then gives `⟪Q, P⟫ ∈ Fq`.
  · intro hwG
    rcases hGMap.1.1 w hwG with ⟨Q, P, hEqw⟩
    subst hEqw
    have hQDomG : Q ∈ dom G := Relation.Pair.mem_dom G Q P hwG
    have hQQuot : Q ∈ A / R ∵ hEqRel := by simpa [(hGMap.2.1 : (dom G) = A / R ∵ hEqRel)] using hQDomG
    rcases (QuotientSet.Spec).1 hQQuot with ⟨x, hxA, hQx⟩
    subst hQx
    clear hQQuot hQDomG
    -- Keep BOTH `IsFunction F` and `x ∈ dom F` in context: every `[F⟮x⟯]₍R₎` below
    -- re-runs `function_eval_auto`, and with both facts available each search closes
    -- by assumption and builds the *same* side-condition proof, so all occurrences
    -- stay syntactically identical and cheap to unify. Without them, reconciling the
    -- two `[F⟮x⟯]₍R₎` terms in the `function_value_unique` call for `hPClass` below
    -- pits two `Classical.choose`-based `FunctionValue` terms against each other and
    -- blows past `maxHeartbeats` — see the "`F⟮x⟯` / `FunctionValue` unification
    -- timeouts" note in `proof_style.md`.
    have hFfun : IsFunction F := hMap.1
    have hxDomF : x ∈ dom F := mapsInto_dom_mem hMap hxA
    have hQyG : ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ G := hGSpec x hxA
    have hPClass : P = [F⟮x⟯]₍R₎ :=
      function_value_unique G ([x]₍R₎) P ([F⟮x⟯]₍R₎) hGMap.1 hwG hQyG
    subst hPClass
    exact hSpec x hxA
  --  • (⊇) every pair of `Fq` has the form `⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫`, which `G`'s
  --    rule also contains.
  · intro hwFq
    rcases hFqFun.1 w hwFq with ⟨Q, P, hEqw⟩
    subst hEqw
    rcases (QuotientLift.Pair.Spec).1 hwFq with
      ⟨_, x, hxA, hQx, hPx⟩
    simpa [hQx, hPx] using hGSpec x hxA

/-- [Enderton Ch3 §6, p.60] "Theorem 3Q (second clause): If `F` is not
compatible with `R`, then no such `F̂ : A / R → A / R` exists." -/
theorem thm_3Q_incompatible_not_exists_quotient_map
  (R A F : Set) (hEqRel : IsEquivalenceRelation R A)
  (hMap : MapsInto F A A) (hNot : ¬ IsCompatible F R A) :
  ¬ ∃ Fq, MapsInto Fq (A / R ∵ hEqRel) (A / R ∵ hEqRel) ∧
    (∀ x (hxA : x ∈ A), ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ Fq) := by
  intro hEx
  rcases hEx with ⟨Fq, hFqMap, hFqSpec⟩
  have hMap' := hMap
  rcases hMap' with ⟨hFfun, hDomF, hRanSubA⟩
  apply hNot
  refine ⟨hMap, ?_⟩
  intro x y hxA hyA hxyR
  have hxDomF : x ∈ dom F := by simpa [hDomF] using hxA
  have hyDomF : y ∈ dom F := by simpa [hDomF] using hyA
  have hClassXY : [x]₍R₎ = [y]₍R₎ := (lem_3N_equiv_class_eq_iff hEqRel hxA hyA).2 hxyR
  have hClassU : ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ Fq := hFqSpec x hxA
  have hClassV : ⟪[y]₍R₎, [F⟮y⟯]₍R₎⟫ ∈ Fq := hFqSpec y hyA
  have hClassV' : ⟪[x]₍R₎, [F⟮y⟯]₍R₎⟫ ∈ Fq := by simpa [hClassXY] using hClassV
  have hClassUV : [F⟮x⟯]₍R₎ = [F⟮y⟯]₍R₎ :=
    function_value_unique Fq ([x]₍R₎) ([F⟮x⟯]₍R₎) ([F⟮y⟯]₍R₎)
      (hFqMap.1 : Fq.IsFunction) hClassU hClassV'  -- key step
  have hFxA : F⟮x⟯ ∈ A := hRanSubA _ (FunctionValue.mem_ran F x hFfun hxDomF)
  have hFyA : F⟮y⟯ ∈ A := hRanSubA _ (FunctionValue.mem_ran F y hFfun hyDomF)
  exact (lem_3N_equiv_class_eq_iff hEqRel hFxA hFyA).1 hClassUV

end Set
