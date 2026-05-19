import Set.Ch4.S2_PeanosPostulates
import Set.Ch3.S4_Functions

/-!
# Chapter 4, Section 3: Recursion on ω

This section formalizes recursion on `ω`, including existence/uniqueness of
recursion solutions and the Peano-system isomorphism theorem (Enderton 4H).

**Construction (Enderton, Ch.4):** for each `n ∈ ω` there is a unique set `g` that is a function
with domain `n⁺`, sends `∅` to `a`, and satisfies the successor clause for every `m ∈ n`. The
recursion solution `h` is the set of pairs `⟪m, v⟫` that appear on some such segment (equivalently:
on the segment indexed by `m`). No Lean `Nat` or `ωCode` bridge is used.
-/

namespace Set

/-
Internal scaffolding (not part of Enderton):
`GraphOn A f` packages a Lean-level operation `f : Set → Set` as a
set-theoretic function `{⟪x, f x⟫ | x ∈ A}` on the carrier `A`. It is the
bridge used by this section's Peano-isomorphism proof (Theorem 4H) and by
the arithmetic recurrences in `Set/Ch4/S4_Arithmetic.lean` to feed a Lean
operation into the recursion theorem (which only accepts set-theoretic
functions). Originally lived in `Set/Ch3/S4_Functions.lean`; moved here to
keep `Set → Set` out of the Enderton-aligned Ch3 layer.
-/
noncomputable def GraphOn (A : Set) (f : Set → Set) : Set :=
  Comprehension
    (fun w => ∃ x, x ∈ A ∧ w = ⟪x, f x⟫)
    (A ⨯ A)

lemma GraphOn.Spec {A : Set} {f : Set → Set} {w : Set} :
    w ∈ GraphOn A f ↔ w ∈ (A ⨯ A) ∧ ∃ x, x ∈ A ∧ w = ⟪x, f x⟫ := by
  simp [GraphOn, Comprehension.Spec]

lemma GraphOn.Pair.Spec {A : Set} {f : Set → Set} (hf : ∀ x, x ∈ A → f x ∈ A) {x y : Set} :
    OrderedPair x y ∈ GraphOn A f ↔ x ∈ A ∧ y = f x := by
  apply Iff.intro
  · intro hxy
    rcases (GraphOn.Spec).1 hxy with ⟨_, hEx⟩
    rcases hEx with ⟨u, huA, hEq⟩
    rw [thm_3A_ordered_pair_uniqueness] at hEq
    rcases hEq with ⟨hxu, hyf⟩
    subst hxu
    exact And.intro huA hyf
  · intro hxy
    rcases hxy with ⟨hxA, hyEq⟩
    have hxfA : f x ∈ A := hf x hxA
    have hGraph : OrderedPair x (f x) ∈ GraphOn A f := by
      exact (GraphOn.Spec).2
        (And.intro ((Product.Pair.Spec).2 ⟨hxA, hxfA⟩) (Exists.intro x (And.intro hxA rfl)))
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
        rcases (Domain.Spec).1 hxDom with ⟨y, hxy⟩
        exact (GraphOn.Pair.Spec hf).1 hxy |>.left
      refine ⟨f x, (GraphOn.Pair.Spec hf).2 (And.intro hxA rfl), ?_⟩
      intro y hxy
      exact (GraphOn.Pair.Spec hf).1 hxy |>.right
  · apply extensionality
    intro x
    apply Iff.intro
    · intro hxDom
      rcases (Domain.Spec).1 hxDom with ⟨y, hxy⟩
      exact (GraphOn.Pair.Spec hf).1 hxy |>.left
    · intro hxA
      exact (Domain.Spec).2
        ⟨f x, (GraphOn.Pair.Spec hf).2 (And.intro hxA rfl)⟩
  · intro y hyRan
    rcases (Range.Spec).1 hyRan with ⟨x, hxy⟩
    rcases (GraphOn.Pair.Spec hf).1 hxy with ⟨hxA, hyEq⟩
    simpa [hyEq] using hf x hxA

def RecursionSolution (h A a F : Set) : Prop :=
  MapsInto h ω A ∧
  ⟪Set.Empty, a⟫ ∈ h ∧
  (∀ n x y, n ∈ ω → ⟪n, x⟫ ∈ h → (⟪n⁺, y⟫ ∈ h ↔ ⟪x, y⟫ ∈ F))

/-- Enderton-style partial segment: a function on domain `n⁺` satisfying the recursion step for
every `m ∈ n` (vacuous when `n = ∅`). -/
private def IsRecursionSegment (A a F : Set) (n : Set) (g : Set) : Prop :=
  n ∈ ω ∧
  IsFunction g ∧
  (Domain g = n⁺) ∧
  OrderedPair Set.Empty a ∈ g ∧
  (∀ (m u v : Set), m ∈ n → OrderedPair m u ∈ g →
    (OrderedPair (m⁺) v ∈ g ↔ OrderedPair u v ∈ F))

private noncomputable def pairGraph (x y : Set) : Set :=
  Singleton (OrderedPair x y)

private lemma pairGraph_spec (x y w : Set) : w ∈ pairGraph x y ↔ w = OrderedPair x y := by
  simp [pairGraph, Singleton.Spec]

private lemma dom_pairGraph (x y : Set) : Domain (pairGraph x y) = Singleton x := by
  apply extensionality
  intro z
  constructor
  · intro hz
    rcases (Domain.Spec).1 hz with ⟨u, hu⟩
    rw [pairGraph_spec] at hu
    rcases (OrderedPair.uniqueness z u x y).1 hu with ⟨hzx, _⟩
    rw [← hzx]
    exact Singleton.Spec.2 rfl
  · intro hz
    rw [Singleton.Spec] at hz
    subst z
    exact (Domain.Spec).2 ⟨y, (pairGraph_spec x y (OrderedPair x y)).2 rfl⟩

private lemma pairGraph_mem (x y : Set) : OrderedPair x y ∈ pairGraph x y :=
  (pairGraph_spec x y (OrderedPair x y)).2 rfl

private lemma isFunction_pairGraph (x y : Set) : IsFunction (pairGraph x y) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [pairGraph_spec] at hw
    subst hw
    exact ⟨x, y, rfl⟩
  · intro z hzDom
    rw [dom_pairGraph] at hzDom
    rw [Singleton.Spec] at hzDom
    subst z
    refine ⟨y, pairGraph_mem x y, ?_⟩
    intro y' hy'
    have hEq : OrderedPair x y' = OrderedPair x y := by simpa [pairGraph_spec] using hy'
    exact (OrderedPair.uniqueness x y' x y).1 hEq |>.2

private lemma dom_empty_pairGraph (a : Set) : Domain (pairGraph Set.Empty a) = Set.Empty⁺ := by
  rw [dom_pairGraph]
  apply extensionality
  intro x
  constructor
  · intro hx
    rw [Singleton.Spec] at hx
    subst x
    rw [Successor, Union.Spec]
    exact Or.inr (Singleton.Spec.2 rfl)
  · intro hx
    rw [Successor, Union.Spec, Singleton.Spec] at hx
    cases hx with
    | inl h => exact (Empty.Spec h).elim
    | inr h =>
      subst x
      exact Singleton.Spec.2 rfl

private lemma recursion_segment_empty (A a F : Set) (ha : a ∈ A) (_hF : MapsInto F A A) :
    IsRecursionSegment A a F Set.Empty (pairGraph Set.Empty a) := by
  refine ⟨thm_4B_ω_inductive.left, isFunction_pairGraph Set.Empty a, ?_, ?_, ?_⟩
  · exact dom_empty_pairGraph a
  · exact pairGraph_mem Set.Empty a
  · intro m u v hm
    exact (Empty.Spec hm).elim

private lemma succ_omega_subset (n : Set) (hn : n ∈ ω) : SubsetOf (n⁺) ω := by
  intro x hx
  exact ω_transitive_set x (n⁺) hx (thm_4B_ω_inductive.right n hn)

private lemma empty_mem_succ_omega (n : Set) (hn : n ∈ ω) : Set.Empty ∈ n⁺ := by
  apply ω_induction (fun k => Set.Empty ∈ k⁺)
  · rw [Successor, Union.Spec]
    exact Or.inr (Singleton.Spec.2 rfl)
  · intro k hkω ih
    exact (mem_successor_iff Set.Empty (k⁺)).2 (Or.inl ih)
  · exact hn

private lemma omega_succ_not_mem_self (n : Set) (hn : n ∈ ω) : n⁺ ∉ n⁺ :=
  natural_not_mem_self (n⁺) (thm_4B_ω_inductive.right n hn)

private lemma mem_pair_union (f1 f2 x y : Set) :
    OrderedPair x y ∈ f1 ∪ f2 ↔ OrderedPair x y ∈ f1 ∨ OrderedPair x y ∈ f2 := by
  simp [Union.Spec]

private lemma union_disjoint_dom_function (f1 f2 : Set)
    (hf1 : IsFunction f1) (hf2 : IsFunction f2)
    (hDisj : ∀ z, z ∈ Domain f1 → z ∈ Domain f2 → False) :
    IsFunction (f1 ∪ f2) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [Union.Spec] at hw
    cases hw with
    | inl hw1 => rcases hf1.1 w hw1 with ⟨x, y, hEq⟩; exact ⟨x, y, hEq⟩
    | inr hw2 => rcases hf2.1 w hw2 with ⟨x, y, hEq⟩; exact ⟨x, y, hEq⟩
  · intro x hxDom
    rcases (Domain.Spec).1 hxDom with ⟨y, hxy⟩
    rcases (mem_pair_union f1 f2 x y).1 hxy with hxy1 | hxy2
    · have hx1 : x ∈ Domain f1 := (Domain.Spec).2 ⟨y, hxy1⟩
      rcases hf1.2 x hx1 with ⟨y1, hy1, hU1⟩
      have hy1y : y1 = y := Eq.symm (hU1 y hxy1)
      subst hy1y
      refine ⟨y1, (mem_pair_union f1 f2 x y1).2 (Or.inl hy1), ?_⟩
      intro y' hy'
      rcases (mem_pair_union f1 f2 x y').1 hy' with hy'1 | hy'2
      · exact hU1 y' hy'1
      · exact False.elim (hDisj x hx1 ((Domain.Spec).2 ⟨y', hy'2⟩))
    · have hx2 : x ∈ Domain f2 := (Domain.Spec).2 ⟨y, hxy2⟩
      rcases hf2.2 x hx2 with ⟨y2, hy2, hU2⟩
      have hy2y : y2 = y := Eq.symm (hU2 y hxy2)
      subst hy2y
      refine ⟨y2, (mem_pair_union f1 f2 x y2).2 (Or.inr hy2), ?_⟩
      intro y' hy'
      rcases (mem_pair_union f1 f2 x y').1 hy' with hy'1 | hy'2
      · exact False.elim (hDisj x ((Domain.Spec).2 ⟨y', hy'1⟩) hx2)
      · exact hU2 y' hy'2

private lemma dom_union_disjoint (f1 f2 : Set)
    (hDisj : ∀ z, z ∈ Domain f1 → z ∈ Domain f2 → False) :
    Domain (f1 ∪ f2) = Domain f1 ∪ Domain f2 := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (Domain.Spec).1 hx with ⟨y, hxy⟩
    rcases (mem_pair_union f1 f2 x y).1 hxy with h1 | h2
    · exact Union.Spec.mpr (Or.inl ((Domain.Spec).2 ⟨y, h1⟩))
    · exact Union.Spec.mpr (Or.inr ((Domain.Spec).2 ⟨y, h2⟩))
  · intro hx
    rw [Union.Spec] at hx
    cases hx with
    | inl hx1 =>
      rcases (Domain.Spec).1 hx1 with ⟨y, hy⟩
      exact (Domain.Spec).2 ⟨y, (mem_pair_union f1 f2 x y).2 (Or.inl hy)⟩
    | inr hx2 =>
      rcases (Domain.Spec).1 hx2 with ⟨y, hy⟩
      exact (Domain.Spec).2 ⟨y, (mem_pair_union f1 f2 x y).2 (Or.inr hy)⟩

private lemma dom_succ_join (n : Set) : n⁺ ∪ Singleton (n⁺) = (n⁺)⁺ := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rw [Union.Spec] at hx
    cases hx with
    | inl h =>
      exact (mem_successor_iff x (n⁺)).2 (Or.inl h)
    | inr h =>
      rw [Singleton.Spec] at h
      subst x
      exact (mem_successor_iff (n⁺) (n⁺)).2 (Or.inr rfl)
  · intro hx
    rcases (mem_successor_iff x (n⁺)).1 hx with hxn | hxeq
    · exact Union.Spec.mpr (Or.inl hxn)
    · subst x
      exact Union.Spec.mpr (Or.inr (Singleton.Spec.2 rfl))

private lemma isFunction_restriction (F : Set) (C : Set) (hF : IsFunction F) : IsFunction (F ↾ C) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    rcases hF.1 w ((Restriction.Spec).1 hw).1 with ⟨x, y, hEq⟩
    exact ⟨x, y, hEq⟩
  · intro x hxDom
    rcases (Domain.Spec).1 hxDom with ⟨y, hxy⟩
    rw [Restriction.Pair.Spec] at hxy
    rcases hxy with ⟨hxyF, hxC⟩
    have hxDF : x ∈ Domain F := (Domain.Spec).2 ⟨y, hxyF⟩
    rcases hF.2 x hxDF with ⟨z, hz, hUz⟩
    refine ⟨z, Restriction.Pair.Spec.mpr ⟨hz, hxC⟩, ?_⟩
    intro z' hz'
    rcases (Restriction.Pair.Spec).1 hz' with ⟨hz'F, _⟩
    exact hUz z' hz'F

private lemma dom_restriction_eq_of_subset (F : Set) (C : Set) (hSub : SubsetOf C (Domain F)) :
    Domain (F ↾ C) = C := by
  apply extensionality
  intro x
  constructor
  · intro hx
    rcases (Domain.Spec).1 hx with ⟨y, hxy⟩
    rw [Restriction.Pair.Spec] at hxy
    exact hxy.2
  · intro hxC
    have hxDF : x ∈ Domain F := hSub x hxC
    rcases (Domain.Spec).1 hxDF with ⟨y, hy⟩
    exact (Domain.Spec).2 ⟨y, Restriction.Pair.Spec.mpr ⟨hy, hxC⟩⟩

private lemma mem_succ_mem_succ_succ (n x : Set) (hx : x ∈ n⁺) : x ∈ (n⁺)⁺ := by
  rcases (mem_successor_iff x n).1 hx with hxn | hxeq
  · exact (mem_successor_iff x (n⁺)).2 (Or.inl ((mem_successor_iff x n).2 (Or.inl hxn)))
  · have hnInSucc : n ∈ n⁺ := by
      rw [hxeq] at hx
      exact hx
    rw [hxeq]
    exact (mem_successor_iff n (n⁺)).2 (Or.inl hnInSucc)

private lemma subset_dom_of_succ_segment (n g : Set) (hn : n ∈ ω) (hDom : Domain g = (n⁺)⁺) :
    SubsetOf (n⁺) (Domain g) := by
  intro x hx
  simpa [hDom] using mem_succ_mem_succ_succ n x hx

private lemma segment_restriction_of_succ (A a F : Set) (n : Set) (hn : n ∈ ω) (g : Set)
    (hSeg : IsRecursionSegment A a F (n⁺) g) :
    IsRecursionSegment A a F n (g ↾ n⁺) := by
  rcases hSeg with ⟨hnSuccω, hFun, hDom, hBase, hRec⟩
  refine ⟨hn, isFunction_restriction g (n⁺) hFun, ?_, ?_, ?_⟩
  · rw [dom_restriction_eq_of_subset g (n⁺) (subset_dom_of_succ_segment n g hn hDom)]
  · rw [Restriction.Pair.Spec]
    exact ⟨hBase, empty_mem_succ_omega n hn⟩
  · intro m u v hmn hmu
    have hmnSucc : m ∈ n⁺ := (mem_successor_iff m n).2 (Or.inl hmn)
    have hmu' : OrderedPair m u ∈ g := (Restriction.Pair.Spec).1 hmu |>.1
    have hRecFull := hRec m u v hmnSucc hmu'
    constructor
    · intro hv
      rw [Restriction.Pair.Spec] at hv
      exact hRecFull.1 hv.1
    · intro hFv
      have hmSuccIn : m⁺ ∈ n⁺ := succ_mem_succ_of_mem m n hn hmn
      exact Restriction.Pair.Spec.mpr ⟨hRecFull.2 hFv, hmSuccIn⟩

private lemma recursion_segment_ran_subset_A (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) :
    ∀ n, n ∈ ω → ∀ g, IsRecursionSegment A a F n g → SubsetOf (ran g) A := by
  intro n hnω g hSeg
  apply (ω_induction (fun t => ∀ g, IsRecursionSegment A a F t g → SubsetOf (ran g) A) ?_ ?_ n hnω) g hSeg
  · intro g' hSeg' y hy
    rcases (Range.Spec).1 hy with ⟨x, hxy⟩
    have hxDom : x ∈ Domain g' := Relation.Pair.mem_dom g' x y hxy
    have hdom : Domain g' = Set.Empty⁺ := hSeg'.2.2.1
    rw [hdom] at hxDom
    rcases (mem_successor_iff x Set.Empty).1 hxDom with hbad | hxE
    · exact (Empty.Spec hbad).elim
    subst hxE
    have hyEq : y = a :=
      function_value_unique g' Set.Empty y a hSeg'.2.1 hxy hSeg'.2.2.2.1
    simpa [hyEq] using ha
  · intro k hkω ih g' hSeg' y hy
    rcases (Range.Spec).1 hy with ⟨x, hxy⟩
    have hxDom : x ∈ Domain g' := Relation.Pair.mem_dom g' x y hxy
    rw [hSeg'.2.2.1] at hxDom
    rcases (mem_successor_iff x (k⁺)).1 hxDom with hxk | hxeq
    · have hRest := segment_restriction_of_succ A a F k hkω g' hSeg'
      have hyRest : y ∈ ran (g' ↾ k⁺) :=
        (Range.Spec).2 ⟨x, Restriction.Pair.Spec.mpr ⟨hxy, hxk⟩⟩
      exact ih (g' ↾ k⁺) hRest y hyRest
    · subst x
      have hkInSuccSucc : k ∈ (k⁺)⁺ :=
        (mem_successor_iff k (k⁺)).2 (Or.inl ((mem_successor_iff k k).2 (Or.inr rfl)))
      have hkDom : k ∈ dom g' := by
        rw [hSeg'.2.2.1]
        exact hkInSuccSucc
      rcases hSeg'.2.1.2 k hkDom with ⟨u, hku, _⟩
      have hkInSk : k ∈ k⁺ := (mem_successor_iff k k).2 (Or.inr rfl)
      have hRec := hSeg'.2.2.2.2 k u y hkInSk hku
      have hyF : OrderedPair u y ∈ F := hRec.1 hxy
      have huA : u ∈ A :=
        ih (g' ↾ k⁺) (segment_restriction_of_succ A a F k hkω g' hSeg') u
          ((Range.Spec).2 ⟨k, Restriction.Pair.Spec.mpr ⟨hku, hkInSk⟩⟩)
      exact hF.2.2 y (Relation.Pair.mem_ran F u y hyF)

private noncomputable def nextValue (A F : Set) (hF : MapsInto F A A) (x : Set) (hxA : x ∈ A) : Set :=
  Classical.choose (ExistsUnique.exists ((hF.1).2 x (by simpa [hF.2.1] using hxA)))

private lemma nextValue_spec (A F : Set) (hF : MapsInto F A A) (x : Set) (hxA : x ∈ A) :
    OrderedPair x (nextValue A F hF x hxA) ∈ F :=
  Classical.choose_spec (ExistsUnique.exists ((hF.1).2 x (by simpa [hF.2.1] using hxA)))

private lemma nextValue_mem (A F : Set) (hF : MapsInto F A A) (x : Set) (hxA : x ∈ A) :
    nextValue A F hF x hxA ∈ A := by
  have hyF : OrderedPair x (nextValue A F hF x hxA) ∈ F := nextValue_spec A F hF x hxA
  have hyRan : nextValue A F hF x hxA ∈ ran F := Relation.Pair.mem_ran F x (nextValue A F hF x hxA) hyF
  exact hF.2.2 (nextValue A F hF x hxA) hyRan

private lemma succ_not_mem_of_mem_omega (n : Set) (hn : n ∈ ω) : n⁺ ∉ n := by
  intro h
  have hnTrans : IsTransitiveSet n := natural_transitive_set n ((ω.Spec).1 hn)
  have hnInN : n ∈ n :=
    hnTrans n (n⁺) ((mem_successor_iff n n).2 (Or.inr rfl)) h
  exact natural_not_mem_self n hn hnInN

private lemma omega_succ_injective (m n : Set) (hm : m ∈ ω) (hn : n ∈ ω) (heq : m⁺ = n⁺) : m = n := by
  have hmTrans : IsTransitiveSet m := natural_transitive_set m ((ω.Spec).1 hm)
  have hnTrans : IsTransitiveSet n := natural_transitive_set n ((ω.Spec).1 hn)
  have hmU : ⋃(m⁺) = m := bigunion_successor_of_transitive m hmTrans
  have hnU : ⋃(n⁺) = n := bigunion_successor_of_transitive n hnTrans
  calc
    m = ⋃(m⁺) := hmU.symm
    _ = ⋃(n⁺) := by simp [heq]
    _ = n := hnU

private lemma succ_ne_succ_of_mem (m p : Set) (hp : p ∈ ω) (hmp : m ∈ p) : m⁺ ≠ p⁺ := by
  intro heq
  have hmω : m ∈ ω := ω_transitive_set m p hmp hp
  have hmEq : m = p := omega_succ_injective m p hmω hp heq
  rw [hmEq] at hmp
  exact absurd hmp (natural_not_mem_self p hp)

private lemma dom_pairGraph_disjoint_segment (n : Set) (hn : n ∈ ω) (g : Set)
    (hDom : Domain g = n⁺) (b : Set) :
    ∀ z, z ∈ Domain g → z ∈ Domain (pairGraph (n⁺) b) → False := by
  intro z hz1 hz2
  rw [hDom] at hz1
  rw [dom_pairGraph, Singleton.Spec] at hz2
  subst z
  exact omega_succ_not_mem_self n hn hz1

/-- Successor clause for `recursion_segment_succ`. Binders `idx` … are introduced before `r` so `r` is not unified with `idx`. -/
private lemma recursion_segment_succ_rec (A a F : Set) (_ha : a ∈ A) (hF : MapsInto F A A) :
    ∀ (idx : Set) (hidx : idx ∈ ω) (g : Set) (hSeg : IsRecursionSegment A a F idx g) (u : Set)
      (hiu : OrderedPair idx u ∈ g) (huA : u ∈ A) (r u' v' : Set),
      r ∈ idx⁺ →
        OrderedPair r u' ∈ (g ∪ pairGraph (idx⁺) (nextValue A F hF u huA)) →
          (OrderedPair (r⁺) v' ∈ (g ∪ pairGraph (idx⁺) (nextValue A F hF u huA)) ↔
            OrderedPair u' v' ∈ F) := by
  intro idx hidx g hSeg u hiu huA r u' v' hrSucc hru'
  let b := nextValue A F hF u huA
  let st := idx⁺
  have hidxInSucc : idx ∈ idx⁺ := (mem_successor_iff idx idx).2 (Or.inr rfl)
  by_cases h : r = idx
  · -- Do not `subst h`: it removes `idx` from the context while we still need it below.
    have hrEq : r = idx := h
    have hrSuccEq : r⁺ = st := by simp [st, hrEq]
    have hruIdx : OrderedPair idx u' ∈ g ∪ pairGraph st b := hrEq ▸ hru'
    have hiuG : OrderedPair idx u' ∈ g := by
      rcases (mem_pair_union g (pairGraph st b) idx u').1 hruIdx with hG | hP
      · exact hG
      · rw [pairGraph_spec] at hP
        have hidxEq : idx = st := (OrderedPair.uniqueness idx u' st b).1 hP |>.1
        simp [st] at hidxEq
        exact False.elim (omega_succ_not_mem_self idx hidx (hidxEq ▸ hidxInSucc))
    have hu'Eq : u' = u := function_value_unique g idx u' u hSeg.2.1 hiuG hiu
    subst u'
    constructor
    · intro hv'
      have hv'2 : OrderedPair (r⁺) v' ∈ g ∪ pairGraph st b := by simpa [st, b] using hv'
      have hvSt : OrderedPair st v' ∈ g ∪ pairGraph st b := hrSuccEq.symm ▸ hv'2
      rcases (mem_pair_union g (pairGraph st b) st v').1 hvSt with hG | hP
      · have : st ∈ Domain g := Relation.Pair.mem_dom g st v' hG
        rw [hSeg.2.2.1] at this
        simp [st] at this
        rcases this with hin | heq
        · exact False.elim (succ_not_mem_of_mem_omega idx hidx hin)
        · rw [heq] at hidxInSucc
          exact absurd hidxInSucc (natural_not_mem_self idx hidx)
      · rw [pairGraph_spec] at hP
        have hvEq : v' = b := (OrderedPair.uniqueness st v' st b).1 hP |>.2
        subst v'
        simpa [b] using nextValue_spec A F hF u huA
    · intro hFv
      have hFb : OrderedPair u b ∈ F := by simpa [b] using nextValue_spec A F hF u huA
      have hv'Eq : v' = b := function_value_unique F u v' b hF.1 hFv hFb
      subst v'
      have hmem : OrderedPair (r⁺) b ∈ g ∪ pairGraph st b :=
        hrSuccEq.symm ▸ (mem_pair_union g (pairGraph st b) st b).2 (Or.inr (pairGraph_mem st b))
      simpa [st, b] using hmem
  · have hri : r ∈ idx := by
      rcases (mem_successor_iff r idx).1 hrSucc with hri | hrEq
      · exact hri
      · exact False.elim (h hrEq)
    have hruG : OrderedPair r u' ∈ g := by
      rcases (mem_pair_union g (pairGraph st b) r u').1 hru' with hG | hP
      · exact hG
      · rw [pairGraph_spec] at hP
        have hrEq' : r = st := (OrderedPair.uniqueness r u' st b).1 hP |>.1
        subst hrEq'
        exact absurd hri (succ_not_mem_of_mem_omega idx hidx)
    have hRec0 := hSeg.2.2.2.2 r u' v' hri hruG
    constructor
    · intro hv'
      rcases (mem_pair_union g (pairGraph st b) (r⁺) v').1 hv' with hG | hP
      · exact hRec0.1 hG
      · rw [pairGraph_spec] at hP
        have hrSuccEq : r⁺ = st := (OrderedPair.uniqueness (r⁺) v' st b).1 hP |>.1
        simp [st] at hrSuccEq
        exact False.elim (succ_ne_succ_of_mem r idx hidx hri hrSuccEq)
    · intro hFv
      exact (mem_pair_union g (pairGraph st b) (r⁺) v').2 (Or.inl (hRec0.2 hFv))

private lemma recursion_segment_succ (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (idx : Set) (hidx : idx ∈ ω)
    (g : Set) (hSeg : IsRecursionSegment A a F idx g) :
    ∃ b, IsRecursionSegment A a F (idx⁺) (g ∪ pairGraph (idx⁺) b) := by
  have hidxInSucc : idx ∈ idx⁺ := (mem_successor_iff idx idx).2 (Or.inr rfl)
  have hidxDom : idx ∈ Domain g := by rw [hSeg.2.2.1]; exact hidxInSucc
  rcases hSeg.2.1.2 idx hidxDom with ⟨u, hiu, _⟩
  have huA : u ∈ A :=
    recursion_segment_ran_subset_A A a F ha hF idx hidx g hSeg u ((Range.Spec).2 ⟨idx, hiu⟩)
  let b := nextValue A F hF u huA
  let st := idx⁺
  let g' := g ∪ pairGraph st b
  refine ⟨b, ⟨thm_4B_ω_inductive.right idx hidx, ?_, ?_, ?_, ?_⟩⟩
  · exact
      union_disjoint_dom_function g (pairGraph st b) hSeg.2.1 (isFunction_pairGraph st b)
        (dom_pairGraph_disjoint_segment idx hidx g hSeg.2.2.1 b)
  · calc
      Domain g' = Domain g ∪ Domain (pairGraph st b) := by
        apply dom_union_disjoint g (pairGraph st b)
        exact dom_pairGraph_disjoint_segment idx hidx g hSeg.2.2.1 b
      _ = idx⁺ ∪ Singleton st := by simp [hSeg.2.2.1, dom_pairGraph, st]
      _ = st⁺ := by simp [st, dom_succ_join]
  · exact (mem_pair_union g (pairGraph st b) Set.Empty a).2 (Or.inl hSeg.2.2.2.1)
  · exact recursion_segment_succ_rec A a F ha hF idx hidx g hSeg u hiu huA

private lemma recursion_segment_exists (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (n : Set) (hn : n ∈ ω) :
    ∃ g, IsRecursionSegment A a F n g := by
  refine ω_induction (fun t => ∃ g, IsRecursionSegment A a F t g) ?_ ?_ n hn
  · exact ⟨pairGraph Set.Empty a, recursion_segment_empty A a F ha hF⟩
  · intro k hkω ⟨g, hSeg⟩
    rcases recursion_segment_succ A a F ha hF k hkω g hSeg with ⟨b, hSucc⟩
    exact ⟨g ∪ pairGraph (k⁺) b, hSucc⟩

private lemma recursion_segment_unique_zero (A a F : Set) (g₁ g₂ : Set)
    (h₁ : IsRecursionSegment A a F Set.Empty g₁) (h₂ : IsRecursionSegment A a F Set.Empty g₂) :
    g₁ = g₂ := by
  apply extensionality
  intro w
  constructor
  · intro hw1
    rcases h₁.2.1.1 w hw1 with ⟨x, y, hwEq⟩
    subst hwEq
    have hxDom : x ∈ Domain g₁ := Relation.Pair.mem_dom g₁ x y hw1
    rw [h₁.2.2.1] at hxDom
    rcases (mem_successor_iff x Set.Empty).1 hxDom with hbad | hxE
    · exact (Empty.Spec hbad).elim
    subst hxE
    have hyEq : y = a := function_value_unique g₁ Set.Empty y a h₁.2.1 hw1 h₁.2.2.2.1
    subst hyEq
    exact h₂.2.2.2.1
  · intro hw2
    rcases h₂.2.1.1 w hw2 with ⟨x, y, hwEq⟩
    subst hwEq
    have hxDom : x ∈ Domain g₂ := Relation.Pair.mem_dom g₂ x y hw2
    rw [h₂.2.2.1] at hxDom
    rcases (mem_successor_iff x Set.Empty).1 hxDom with hbad | hxE
    · exact (Empty.Spec hbad).elim
    subst hxE
    have hyEq : y = a := function_value_unique g₂ Set.Empty y a h₂.2.1 hw2 h₂.2.2.2.1
    subst hyEq
    exact h₁.2.2.2.1

private lemma recursion_segment_succ_top_transfer (A a F : Set) (hF : MapsInto F A A)
    (k : Set) (hkω : k ∈ ω) (g₁' g₂' : Set)
    (h₁' : IsRecursionSegment A a F (k⁺) g₁') (h₂' : IsRecursionSegment A a F (k⁺) g₂')
    (hReq : g₁' ↾ k⁺ = g₂' ↾ k⁺) (y : Set) :
    OrderedPair (k⁺) y ∈ g₁' → OrderedPair (k⁺) y ∈ g₂' := by
  intro hkpy
  have hkInSucc : k ∈ k⁺ := (mem_successor_iff k k).2 (Or.inr rfl)
  have hkDom₁ : k ∈ Domain g₁' := by
    rw [h₁'.2.2.1]
    exact mem_succ_mem_succ_succ k k hkInSucc
  have hkDom₂ : k ∈ Domain g₂' := by
    rw [h₂'.2.2.1]
    exact mem_succ_mem_succ_succ k k hkInSucc
  rcases h₁'.2.1.2 k hkDom₁ with ⟨u, hku, _⟩
  rcases h₂'.2.1.2 k hkDom₂ with ⟨u₂, hku₂, _⟩
  have hkuR₁ : OrderedPair k u ∈ g₁' ↾ k⁺ := Restriction.Pair.Spec.mpr ⟨hku, hkInSucc⟩
  have hkuR₂ : OrderedPair k u₂ ∈ g₂' ↾ k⁺ := Restriction.Pair.Spec.mpr ⟨hku₂, hkInSucc⟩
  have hkuR₂' : OrderedPair k u ∈ g₂' ↾ k⁺ := by
    simpa [hReq] using hkuR₁
  have huEq : u = u₂ :=
    function_value_unique (g₂' ↾ k⁺) k u u₂ (isFunction_restriction g₂' (k⁺) h₂'.2.1) hkuR₂' hkuR₂
  subst u₂
  have hkTopDom₂ : k⁺ ∈ Domain g₂' := by
    rw [h₂'.2.2.1]
    exact (mem_successor_iff (k⁺) (k⁺)).2 (Or.inr rfl)
  rcases h₂'.2.1.2 (k⁺) hkTopDom₂ with ⟨y₂, hkpy₂, _⟩
  have hkuG₂ : OrderedPair k u ∈ g₂' := (Restriction.Pair.Spec).1 hkuR₂' |>.1
  have hiff₁ := h₁'.2.2.2.2 k u y hkInSucc hku
  have hiff₂ := h₂'.2.2.2.2 k u y₂ hkInSucc hkuG₂
  have hFuy : OrderedPair u y ∈ F := hiff₁.1 hkpy
  have hFuy₂ : OrderedPair u y₂ ∈ F := hiff₂.1 hkpy₂
  have hyEq : y = y₂ := function_value_unique F u y y₂ hF.1 hFuy hFuy₂
  subst y₂
  exact hkpy₂

private lemma recursion_segment_unique (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (n : Set) (hn : n ∈ ω)
    (g₁ g₂ : Set) (h₁ : IsRecursionSegment A a F n g₁) (h₂ : IsRecursionSegment A a F n g₂) :
    g₁ = g₂ := by
  refine
    ω_induction
      (fun t => ∀ g₁ g₂, IsRecursionSegment A a F t g₁ → IsRecursionSegment A a F t g₂ → g₁ = g₂) ?_ ?_ n hn g₁ g₂ h₁
      h₂
  · intro g₁' g₂' h₁' h₂'
    exact recursion_segment_unique_zero A a F g₁' g₂' h₁' h₂'
  · intro k hkω ih g₁' g₂' h₁' h₂'
    have hr₁ := segment_restriction_of_succ A a F k hkω g₁' h₁'
    have hr₂ := segment_restriction_of_succ A a F k hkω g₂' h₂'
    have hReq : g₁' ↾ k⁺ = g₂' ↾ k⁺ := ih (g₁' ↾ k⁺) (g₂' ↾ k⁺) hr₁ hr₂
    apply extensionality
    intro w
    constructor
    · intro hw1
      rcases h₁'.2.1.1 w hw1 with ⟨x, y, hwEq⟩
      subst hwEq
      have hxdom : x ∈ Domain g₁' := Relation.Pair.mem_dom g₁' x y hw1
      rw [h₁'.2.2.1] at hxdom
      rcases (mem_successor_iff x (k⁺)).1 hxdom with hxk | hxeq
      · have hwR : OrderedPair x y ∈ g₁' ↾ k⁺ := Restriction.Pair.Spec.mpr ⟨hw1, hxk⟩
        have hwR' : OrderedPair x y ∈ g₂' ↾ k⁺ := by simpa [hReq] using hwR
        exact (Restriction.Pair.Spec).1 hwR' |>.1
      · subst x
        exact recursion_segment_succ_top_transfer A a F hF k hkω g₁' g₂' h₁' h₂' hReq y hw1
    · intro hw2
      rcases h₂'.2.1.1 w hw2 with ⟨x, y, hwEq⟩
      subst hwEq
      have hxdom : x ∈ Domain g₂' := Relation.Pair.mem_dom g₂' x y hw2
      rw [h₂'.2.2.1] at hxdom
      rcases (mem_successor_iff x (k⁺)).1 hxdom with hxk | hxeq
      · have hwR : OrderedPair x y ∈ g₂' ↾ k⁺ := Restriction.Pair.Spec.mpr ⟨hw2, hxk⟩
        have hwR' : OrderedPair x y ∈ g₁' ↾ k⁺ := by simpa [hReq] using hwR
        exact (Restriction.Pair.Spec).1 hwR' |>.1
      · subst x
        exact recursion_segment_succ_top_transfer A a F hF k hkω g₂' g₁' h₂' h₁' hReq.symm y hw2

private lemma recursion_segment_tail_eq (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (n : Set) (hn : n ∈ ω)
    (g : Set) (hSeg : IsRecursionSegment A a F n g) (g' : Set) (hSeg' : IsRecursionSegment A a F (n⁺) g') :
    g = g' ↾ n⁺ := by
  have hRest := segment_restriction_of_succ A a F n hn g' hSeg'
  exact (recursion_segment_unique A a F ha hF n hn g (g' ↾ n⁺) hSeg hRest)

private noncomputable def recursionGraph (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) : Set :=
  Comprehension
    (fun w =>
      ∃ (m v : Set), m ∈ ω ∧ w = OrderedPair m v ∧ ∃ g, IsRecursionSegment A a F m g ∧ OrderedPair m v ∈ g)
    (ω ⨯ A)

private lemma recursionGraph_spec (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (w : Set) :
    w ∈ recursionGraph A a F ha hF ↔
      w ∈ (ω ⨯ A) ∧
        ∃ (m v : Set), m ∈ ω ∧ w = OrderedPair m v ∧ ∃ g, IsRecursionSegment A a F m g ∧ OrderedPair m v ∈ g := by
  simp [recursionGraph, Comprehension.Spec]

private lemma recursionGraph_pair_mem (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (m v : Set) (hmω : m ∈ ω)
    (hvA : v ∈ A) (g : Set) (hg : IsRecursionSegment A a F m g) (hmv : OrderedPair m v ∈ g) :
    OrderedPair m v ∈ recursionGraph A a F ha hF := by
  refine (recursionGraph_spec A a F ha hF (OrderedPair m v)).2 ⟨?_, m, v, hmω, rfl, g, hg, hmv⟩
  exact (Product.Pair.Spec).2 ⟨hmω, hvA⟩

private lemma recursionGraph_pair_witness (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (x y : Set) :
    OrderedPair x y ∈ recursionGraph A a F ha hF →
      x ∈ ω ∧ ∃ g, IsRecursionSegment A a F x g ∧ OrderedPair x y ∈ g := by
  intro hxy
  rcases (recursionGraph_spec A a F ha hF (OrderedPair x y)).1 hxy with ⟨_, m, v, hmω, hEq, g, hg, hmv⟩
  rcases (OrderedPair.uniqueness x y m v).1 hEq with ⟨hxm, hyv⟩
  subst hxm hyv
  exact ⟨hmω, g, hg, hmv⟩

private lemma recursionGraph_dom_ran_aux (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (x y : Set)
    (hxy : OrderedPair x y ∈ recursionGraph A a F ha hF) : x ∈ ω ∧ y ∈ A := by
  rcases (recursionGraph_spec A a F ha hF (OrderedPair x y)).1 hxy with ⟨hProd, _, _, _, _, _, _, _⟩
  exact (Product.Pair.Spec).1 hProd

private lemma recursionGraph_value_unique (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (m : Set) (hmω : m ∈ ω)
    (y₁ y₂ : Set) (hy₁ : OrderedPair m y₁ ∈ recursionGraph A a F ha hF)
    (hy₂ : OrderedPair m y₂ ∈ recursionGraph A a F ha hF) : y₁ = y₂ := by
  rcases recursionGraph_pair_witness A a F ha hF m y₁ hy₁ with ⟨_, g₁, hSeg₁, hmy₁⟩
  rcases recursionGraph_pair_witness A a F ha hF m y₂ hy₂ with ⟨_, g₂, hSeg₂, hmy₂⟩
  have hEq := recursion_segment_unique A a F ha hF m hmω g₁ g₂ hSeg₁ hSeg₂
  subst hEq
  exact function_value_unique g₁ m y₁ y₂ hSeg₁.2.1 hmy₁ hmy₂

/- [Enderton, Recursion Theorem on ω (existence), pp.73-79] -/
theorem recursion_exists_on_ω (A a F : Set) : a ∈ A → MapsInto F A A → ∃ h, RecursionSolution h A a F := by
  intro ha hF
  let h := recursionGraph A a F ha hF
  refine ⟨h, ?_⟩
  unfold RecursionSolution
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · intro w hw
    rcases (recursionGraph_spec A a F ha hF w).1 hw with ⟨_, m, v, _, hwEq, _, _, _⟩
    exact ⟨m, v, hwEq⟩
  · intro x hxDom
    rcases (Domain.Spec).1 hxDom with ⟨y₀, hy₀⟩
    rcases recursionGraph_pair_witness A a F ha hF x y₀ hy₀ with ⟨hxω, g₀, hSeg₀, hx₀⟩
    refine ⟨y₀, hy₀, ?_⟩
    intro y hy
    exact recursionGraph_value_unique A a F ha hF x hxω y y₀ hy hy₀
  · apply extensionality
    intro x
    constructor
    · intro hxDom
      rcases (Domain.Spec).1 hxDom with ⟨y, hxy⟩
      exact (recursionGraph_dom_ran_aux A a F ha hF x y hxy).1
    · intro hxω
      rcases recursion_segment_exists A a F ha hF x hxω with ⟨g, hSeg⟩
      have hxInDom : x ∈ Domain g := by rw [hSeg.2.2.1]; exact (mem_successor_iff x x).2 (Or.inr rfl)
      rcases hSeg.2.1.2 x hxInDom with ⟨v, hxv, _⟩
      have hvA : v ∈ A := recursion_segment_ran_subset_A A a F ha hF x hxω g hSeg v ((Range.Spec).2 ⟨x, hxv⟩)
      exact (Domain.Spec).2 ⟨v, recursionGraph_pair_mem A a F ha hF x v hxω hvA g hSeg hxv⟩
  · intro y hyRan
    rcases (Range.Spec).1 hyRan with ⟨x, hxy⟩
    exact (recursionGraph_dom_ran_aux A a F ha hF x y hxy).2
  · rcases recursion_segment_exists A a F ha hF Set.Empty thm_4B_ω_inductive.left with ⟨g₀, hSeg₀⟩
    exact recursionGraph_pair_mem A a F ha hF Set.Empty a thm_4B_ω_inductive.left ha g₀ hSeg₀ hSeg₀.2.2.2.1
  · intro n x y hnω hnx
    rcases recursion_segment_exists A a F ha hF n hnω with ⟨gₙ, hSegₙ⟩
    rcases recursion_segment_exists A a F ha hF (n⁺) (thm_4B_ω_inductive.right n hnω) with ⟨gₛ, hSegₛ⟩
    have hTail := recursion_segment_tail_eq A a F ha hF n hnω gₙ hSegₙ gₛ hSegₛ
    have hnxₛ : OrderedPair n x ∈ gₛ := by
      have hmem : OrderedPair n x ∈ gₛ ↾ n⁺ := by
        have hgr : OrderedPair n x ∈ recursionGraph A a F ha hF := hnx
        rcases recursionGraph_pair_witness A a F ha hF n x hgr with ⟨_, g', hSeg', hnxg'⟩
        have hU := recursion_segment_unique A a F ha hF n hnω gₙ g' hSegₙ hSeg'
        have hnxgₙ : OrderedPair n x ∈ gₙ := by
          rw [Eq.symm hU] at hnxg'
          exact hnxg'
        rw [hTail] at hnxgₙ
        exact hnxgₙ
      exact (Restriction.Pair.Spec).1 hmem |>.1
    have hRecₛ := hSegₛ.2.2.2.2 n x y ((mem_successor_iff n n).2 (Or.inr rfl)) hnxₛ
    constructor
    · intro hny
      have hny' : OrderedPair (n⁺) y ∈ gₛ := by
        have hgr : OrderedPair (n⁺) y ∈ recursionGraph A a F ha hF := hny
        rcases recursionGraph_pair_witness A a F ha hF (n⁺) y hgr with ⟨_, g', hSeg', hnyg'⟩
        have hU := recursion_segment_unique A a F ha hF (n⁺) (thm_4B_ω_inductive.right n hnω) gₛ g' hSegₛ hSeg'
        subst hU
        exact hnyg'
      exact hRecₛ.1 hny'
    · intro hFxy
      have hnyg : OrderedPair (n⁺) y ∈ gₛ := hRecₛ.2 hFxy
      have hvA : y ∈ A := recursion_segment_ran_subset_A A a F ha hF (n⁺) (thm_4B_ω_inductive.right n hnω) gₛ hSegₛ y
        ((Range.Spec).2 ⟨n⁺, hnyg⟩)
      exact recursionGraph_pair_mem A a F ha hF (n⁺) y (thm_4B_ω_inductive.right n hnω) hvA gₛ hSegₛ hnyg

/- [Enderton, Recursion Theorem on ω (uniqueness), pp.73-79] -/
theorem recursion_solution_unique
  (A a F h₁ h₂ : Set)
  (hF : MapsInto F A A)
  (hh₁ : RecursionSolution h₁ A a F)
  (hh₂ : RecursionSolution h₂ A a F) :
  h₁ = h₂ := by
  rcases hh₁ with ⟨h₁Into, h₁Base, h₁Rec⟩
  rcases hh₂ with ⟨h₂Into, h₂Base, h₂Rec⟩
  have hFfun : IsFunction F := hF.1
  have h₁Fun : IsFunction h₁ := h₁Into.1
  have h₂Fun : IsFunction h₂ := h₂Into.1
  have h₁Dom : (dom h₁) = ω := h₁Into.2.1
  have h₂Dom : (dom h₂) = ω := h₂Into.2.1
  have hT : ∃ (T : Set), ∀ (n : Set), n ∈ T ↔ n ∈ ω ∧ ∀ x y, OrderedPair n x ∈ h₁ → OrderedPair n y ∈ h₂ → x = y := by
    apply comprehension
  obtain ⟨T, hTspec⟩ := hT
  have hTind : Inductive T := by
    rw [Inductive]
    refine ⟨?_, ?_⟩
    · have h0eq : ∀ x y, OrderedPair Set.Empty x ∈ h₁ → OrderedPair Set.Empty y ∈ h₂ → x = y := by
        intro x y hx hy
        have hxa : x = a := function_value_unique h₁ Set.Empty x a h₁Fun hx h₁Base
        have hya : y = a := function_value_unique h₂ Set.Empty y a h₂Fun hy h₂Base
        exact hxa.trans hya.symm
      exact (hTspec Set.Empty).2 ⟨thm_4B_ω_inductive.left, h0eq⟩
    · intro n hnT
      rcases (hTspec n).1 hnT with ⟨hnω, hIndEq⟩
      have hnSuccω : n⁺ ∈ ω := thm_4B_ω_inductive.right n hnω
      have hSuccEq : ∀ x y, OrderedPair (n⁺) x ∈ h₁ → OrderedPair (n⁺) y ∈ h₂ → x = y := by
        intro x y hx hy
        have hnDom₁ : n ∈ dom h₁ := by simpa [h₁Dom] using hnω
        have hnDom₂ : n ∈ dom h₂ := by simpa [h₂Dom] using hnω
        rcases h₁Fun.2 n hnDom₁ with ⟨u, hu, _⟩
        rcases h₂Fun.2 n hnDom₂ with ⟨v, hv, _⟩
        have hux : OrderedPair u x ∈ F := (h₁Rec n u x hnω hu).1 hx
        have hvy : OrderedPair v y ∈ F := (h₂Rec n v y hnω hv).1 hy
        have huv : u = v := hIndEq u v hu hv
        have hvx : OrderedPair v x ∈ F := by simpa [huv] using hux
        exact function_value_unique F v x y hFfun hvx hvy
      exact (hTspec (n⁺)).2 ⟨hnSuccω, hSuccEq⟩
  have hAgree : ∀ n, n ∈ ω → ∀ x y, OrderedPair n x ∈ h₁ → OrderedPair n y ∈ h₂ → x = y := by
    intro n hnω x y hx hy
    have hnT : n ∈ T := (ω.Spec).1 hnω T hTind
    exact (hTspec n).1 hnT |>.2 x y hx hy
  apply extensionality
  intro w
  constructor
  · intro hw₁
    rcases h₁Fun.1 w hw₁ with ⟨n, x, hwEq₁⟩
    subst hwEq₁
    have hnDom₁ : n ∈ dom h₁ := Relation.Pair.mem_dom h₁ n x hw₁
    have hnω : n ∈ ω := by simpa [h₁Dom] using hnDom₁
    have hnDom₂ : n ∈ dom h₂ := by simpa [h₂Dom] using hnω
    rcases h₂Fun.2 n hnDom₂ with ⟨y, hy, _⟩
    have hxy : x = y := hAgree n hnω x y hw₁ hy
    simpa [hxy] using hy
  · intro hw₂
    rcases h₂Fun.1 w hw₂ with ⟨n, y, hwEq₂⟩
    subst hwEq₂
    have hnDom₂ : n ∈ dom h₂ := Relation.Pair.mem_dom h₂ n y hw₂
    have hnω : n ∈ ω := by simpa [h₂Dom] using hnDom₂
    have hnDom₁ : n ∈ dom h₁ := by simpa [h₁Dom] using hnω
    rcases h₁Fun.2 n hnDom₁ with ⟨x, hx, _⟩
    have hxy : x = y := hAgree n hnω x y hx hw₂
    simpa [hxy] using hx

/- [Enderton, Recursion Theorem on ω (existence and uniqueness), pp.73-79] -/
theorem recursion_theorem_on_ω
  (A a F : Set) :
  a ∈ A →
  MapsInto F A A →
  ∃! h, RecursionSolution h A a F := by
  intro ha hF
  rcases recursion_exists_on_ω A a F ha hF with ⟨h, hh⟩
  refine ⟨h, hh, ?_⟩
  intro h' hh'
  exact (recursion_solution_unique A a F h h' hF hh hh').symm

def IsPeanoIsomorphism (f N : Set) (S : Set → Set) (e : Set) : Prop :=
  MapsOnto f ω N ∧
  ⟪Set.Empty, e⟫ ∈ f ∧
  (∀ n x y, n ∈ ω → ⟪n, x⟫ ∈ f → (⟪n⁺, y⟫ ∈ f ↔ y = S x))

/- [Enderton, Theorem 4H, pp.78-79] -/
theorem thm_4H_peano_isomorphic
  (N : Set) (S : Set → Set) (e : Set) :
  IsPeanoSystem N S e →
  ∃ f, IsPeanoIsomorphism f N S e := by
  intro hPeano
  rcases hPeano with ⟨heN, hSClosed, _hSNe, _hSInj, hInd⟩
  let F : Set := GraphOn N S
  have hFmaps : MapsInto F N N := by
    simpa [F] using (GraphOn.mapsInto N S hSClosed)
  rcases recursion_theorem_on_ω N e F heN hFmaps with ⟨h, hhSol, _hhUniq⟩
  have hInto : MapsInto h ω N := hhSol.1
  have hBase : OrderedPair Set.Empty e ∈ h := hhSol.2.1
  have hRec : ∀ n x y, n ∈ ω → OrderedPair n x ∈ h → (OrderedPair (n⁺) y ∈ h ↔ OrderedPair x y ∈ F) := hhSol.2.2
  have hRanSub : SubsetOf (Range h) N := hInto.2.2
  have heRan : e ∈ Range h := (Range.Spec).2 ⟨Set.Empty, hBase⟩
  have hRanClosed : ∀ x, x ∈ Range h → S x ∈ Range h := by
    intro x hxRan
    rcases (Range.Spec).1 hxRan with ⟨n, hnx⟩
    have hnDom : n ∈ dom h := Relation.Pair.mem_dom h n x hnx
    have hnω : n ∈ ω := by simpa [hInto.2.1] using hnDom
    have hxN : x ∈ N := hRanSub x hxRan
    have hxGraph : OrderedPair x (S x) ∈ F := by
      have hG : OrderedPair x (S x) ∈ GraphOn N S :=
        (GraphOn.Pair.Spec hSClosed).2 ⟨hxN, rfl⟩
      simpa [F] using hG
    have hNext : OrderedPair (n⁺) (S x) ∈ h := (hRec n x (S x) hnω hnx).2 hxGraph
    exact (Range.Spec).2 ⟨n⁺, hNext⟩
  have hRanEq : Range h = N := hInd (Range h) hRanSub heRan hRanClosed
  have hOnto : MapsOnto h ω N := ⟨hInto, hRanEq⟩
  refine ⟨h, ?_⟩
  refine ⟨hOnto, hBase, ?_⟩
  intro n x y hnω hnx
  have hxRan : x ∈ Range h := Relation.Pair.mem_ran h n x hnx
  have hxN : x ∈ N := by simpa [hRanEq] using hxRan
  have hGraphIff : OrderedPair x y ∈ F ↔ y = S x := by
    constructor
    · intro hxyF
      have hxyG : OrderedPair x y ∈ GraphOn N S := by simpa [F] using hxyF
      exact (GraphOn.Pair.Spec hSClosed).1 hxyG |>.right
    · intro hyEq
      have hxyG : OrderedPair x y ∈ GraphOn N S :=
        (GraphOn.Pair.Spec hSClosed).2 ⟨hxN, hyEq⟩
      simpa [F] using hxyG
  constructor
  · intro hny
    exact hGraphIff.mp ((hRec n x y hnω hnx).1 hny)
  · intro hyEq
    exact (hRec n x y hnω hnx).2 (hGraphIff.mpr hyEq)

end Set
