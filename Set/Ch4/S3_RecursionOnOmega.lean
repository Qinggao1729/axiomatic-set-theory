import Set.Ch4.S2_PeanosPostulates
import Set.Ch3.S4_Functions

/-!
# Chapter 4, Section 3: Recursion on ω

This section formalizes recursion on `ω`, including existence/uniqueness of
recursion solutions and the Peano-system isomorphism theorem (Enderton 4H).
-/

namespace Set

def RecursionSolution (h A a F : Set) : Prop :=
  MapsInto h ω A ∧
  ⟨Set.Empty, a⟩ ∈ h ∧
  (∀ n x y, n ∈ ω → ⟨n, x⟩ ∈ h → (⟨n⁺, y⟩ ∈ h ↔ ⟨x, y⟩ ∈ F))

noncomputable def ωCode : Nat → Set
  | Nat.zero => Set.Empty
  | Nat.succ n => (ωCode n)⁺

lemma ωCode_mem_ω : ∀ n : Nat, ωCode n ∈ ω := by
  intro n
  induction n with
  | zero =>
      simpa [ωCode] using ω.inductive.left
  | succ n ih =>
      simpa [ωCode] using ω.inductive.right (ωCode n) ih

lemma ωCode_injective : ∀ m n : Nat, ωCode m = ωCode n → m = n := by
  intro m
  induction m with
  | zero =>
      intro n hEq
      cases n with
      | zero =>
          rfl
      | succ n =>
          have hne : ωCode (Nat.succ n) ≠ Set.Empty := by
            simpa [ωCode] using successor_ne_empty (ωCode n)
          exfalso
          exact hne (by simpa [ωCode] using hEq.symm)
  | succ m ihm =>
      intro n hEq
      cases n with
      | zero =>
          have hne : ωCode (Nat.succ m) ≠ Set.Empty := by
            simpa [ωCode] using successor_ne_empty (ωCode m)
          exfalso
          exact hne (by simpa [ωCode] using hEq)
      | succ n =>
          have hmω : ωCode m ∈ ω := ωCode_mem_ω m
          have hnω : ωCode n ∈ ω := ωCode_mem_ω n
          have hSuccInj : ∀ u v, u ∈ ω → v ∈ ω → u⁺ = v⁺ → u = v := (omega_peano_system).2.2.2.1
          have hPred : ωCode m = ωCode n := by
            apply hSuccInj (ωCode m) (ωCode n) hmω hnω
            simpa [ωCode] using hEq
          exact congrArg Nat.succ (ihm n hPred)

theorem ωCode_surjective (x : Set) : x ∈ ω → ∃ n : Nat, ωCode n = x := by
  intro hxω
  have hT : ∃ (T : Set), ∀ (z : Set), z ∈ T ↔ z ∈ ω ∧ ∃ n : Nat, ωCode n = z := by
    apply comprehension
  obtain ⟨T, hTspec⟩ := hT
  have hTind : Inductive T := by
    rw [Inductive]
    refine ⟨?_, ?_⟩
    · exact (hTspec Set.Empty).2 ⟨ω.inductive.left, ⟨Nat.zero, rfl⟩⟩
    · intro z hz
      rcases (hTspec z).1 hz with ⟨hzω, ⟨n, hn⟩⟩
      have hzSuccω : z⁺ ∈ ω := ω.inductive.right z hzω
      exact (hTspec (z⁺)).2 ⟨hzSuccω, ⟨Nat.succ n, by simp [ωCode, hn]⟩⟩
  have hxNat : Natural x := (ω.Spec).1 hxω
  have hxT : x ∈ T := hxNat T hTind
  exact (hTspec x).1 hxT |>.right

noncomputable def nextValue (A F : Set) (hF : MapsInto F A A) (x : Set) (hxA : x ∈ A) : Set :=
  Classical.choose (ExistsUnique.exists ((hF.1).2 x (by simpa [hF.2.1] using hxA)))

lemma nextValue_spec (A F : Set) (hF : MapsInto F A A) (x : Set) (hxA : x ∈ A) :
    OrderedPair x (nextValue A F hF x hxA) ∈ F := by
  exact Classical.choose_spec (ExistsUnique.exists ((hF.1).2 x (by simpa [hF.2.1] using hxA)))

lemma nextValue_mem (A F : Set) (hF : MapsInto F A A) (x : Set) (hxA : x ∈ A) :
    nextValue A F hF x hxA ∈ A := by
  have hyF : OrderedPair x (nextValue A F hF x hxA) ∈ F := nextValue_spec A F hF x hxA
  have hyRan : nextValue A F hF x hxA ∈ ran F := Pair.mem_ran F x (nextValue A F hF x hxA) hyF
  exact hF.2.2 (nextValue A F hF x hxA) hyRan

noncomputable def recursionNatPair (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) : Nat → {x : Set // x ∈ A}
  | Nat.zero => ⟨a, ha⟩
  | Nat.succ n =>
      let p := recursionNatPair A a F ha hF n
      ⟨nextValue A F hF p.1 p.2, nextValue_mem A F hF p.1 p.2⟩

noncomputable def recursionNatVal (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (n : Nat) : Set :=
  (recursionNatPair A a F ha hF n).1

lemma recursionNatVal_mem (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (n : Nat) :
    recursionNatVal A a F ha hF n ∈ A := by
  exact (recursionNatPair A a F ha hF n).2

lemma recursionNatVal_step (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (n : Nat) :
    OrderedPair (recursionNatVal A a F ha hF n) (recursionNatVal A a F ha hF (Nat.succ n)) ∈ F := by
  simp [recursionNatVal, recursionNatPair, nextValue_spec]

noncomputable def recursionGraph (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) : Set :=
  Comprehension
    (fun w => ∃ n : Nat, w = OrderedPair (ωCode n) (recursionNatVal A a F ha hF n))
    (ω ⨯ A)

lemma recursionGraph_spec (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) :
    ∀ w, w ∈ recursionGraph A a F ha hF ↔
      w ∈ (ω ⨯ A) ∧ ∃ n : Nat, w = OrderedPair (ωCode n) (recursionNatVal A a F ha hF n) := by
  intro w
  simp [recursionGraph, Comprehension.Spec]

lemma recursionGraph_pair_witness (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (x y : Set) :
    OrderedPair x y ∈ recursionGraph A a F ha hF →
    ∃ n : Nat, x = ωCode n ∧ y = recursionNatVal A a F ha hF n := by
  intro hxy
  rcases (recursionGraph_spec A a F ha hF (OrderedPair x y)).1 hxy with ⟨_, ⟨n, hEq⟩⟩
  have hUniq := (OrderedPair.uniqueness x y (ωCode n) (recursionNatVal A a F ha hF n)).1 hEq
  exact ⟨n, hUniq.1, hUniq.2⟩

lemma recursionGraph_pair_intro (A a F : Set) (ha : a ∈ A) (hF : MapsInto F A A) (n : Nat) :
    OrderedPair (ωCode n) (recursionNatVal A a F ha hF n) ∈ recursionGraph A a F ha hF := by
  have hnω : ωCode n ∈ ω := ωCode_mem_ω n
  have hnA : recursionNatVal A a F ha hF n ∈ A := recursionNatVal_mem A a F ha hF n
  exact (recursionGraph_spec A a F ha hF (OrderedPair (ωCode n) (recursionNatVal A a F ha hF n))).2
    ⟨Pair.mem_product ω A (ωCode n) (recursionNatVal A a F ha hF n) hnω hnA, ⟨n, rfl⟩⟩

theorem recursion_exists_on_ω
  (A a F : Set) :
  a ∈ A →
  MapsInto F A A →
  ∃ h, RecursionSolution h A a F := by
  intro ha hF
  let h : Set := recursionGraph A a F ha hF
  refine ⟨h, ?_⟩
  unfold RecursionSolution
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro w hw
        rcases (recursionGraph_spec A a F ha hF w).1 hw with ⟨_, ⟨n, hEq⟩⟩
        exact ⟨ωCode n, recursionNatVal A a F ha hF n, hEq⟩
      · intro x hxDom
        rcases (Relation.Domain.Spec).1 hxDom with ⟨y₀, hy₀⟩
        rcases recursionGraph_pair_witness A a F ha hF x y₀ hy₀ with ⟨n₀, hxn₀, hy₀eq⟩
        refine ⟨recursionNatVal A a F ha hF n₀, ?_, ?_⟩
        · have hPair := recursionGraph_pair_intro A a F ha hF n₀
          simpa [hxn₀, hy₀eq] using hPair
        · intro y hy
          rcases recursionGraph_pair_witness A a F ha hF x y hy with ⟨n, hxn, hyEq⟩
          have hnEq : n = n₀ := by
            apply ωCode_injective n n₀
            calc
              ωCode n = x := hxn.symm
              _ = ωCode n₀ := hxn₀
          simpa [hnEq] using hyEq
    · apply extensionality
      intro x
      constructor
      · intro hxDom
        rcases (Relation.Domain.Spec).1 hxDom with ⟨y, hxy⟩
        rcases recursionGraph_pair_witness A a F ha hF x y hxy with ⟨n, hxn, _⟩
        simpa [hxn] using ωCode_mem_ω n
      · intro hxω
        rcases ωCode_surjective x hxω with ⟨n, hxn⟩
        have hPair : OrderedPair x (recursionNatVal A a F ha hF n) ∈ h := by
          have hRaw := recursionGraph_pair_intro A a F ha hF n
          simpa [hxn] using hRaw
        exact (Relation.Domain.Spec).2 ⟨recursionNatVal A a F ha hF n, hPair⟩
    · intro y hyRan
      rcases (Relation.Range.Spec).1 hyRan with ⟨x, hxy⟩
      rcases recursionGraph_pair_witness A a F ha hF x y hxy with ⟨n, _, hyEq⟩
      simpa [hyEq] using recursionNatVal_mem A a F ha hF n
  · have hBasePair := recursionGraph_pair_intro A a F ha hF Nat.zero
    simpa [h, ωCode, recursionNatVal, recursionNatPair] using hBasePair
  · intro n x y hnω hnx
    rcases recursionGraph_pair_witness A a F ha hF n x hnx with ⟨i, hni, hxi⟩
    have hFfun : IsFunction F := hF.1
    constructor
    · intro hny
      rcases recursionGraph_pair_witness A a F ha hF (n⁺) y hny with ⟨j, hnj, hyj⟩
      have hjEq : j = Nat.succ i := by
        apply ωCode_injective j (Nat.succ i)
        calc
          ωCode j = n⁺ := hnj.symm
          _ = (ωCode i)⁺ := by simp [hni]
          _ = ωCode (Nat.succ i) := by simp [ωCode]
      have hyStep : y = recursionNatVal A a F ha hF (Nat.succ i) := by simpa [hjEq] using hyj
      have hStepF : OrderedPair (recursionNatVal A a F ha hF i) (recursionNatVal A a F ha hF (Nat.succ i)) ∈ F :=
        recursionNatVal_step A a F ha hF i
      simpa [hxi, hyStep] using hStepF
    · intro hxyF
      have hxyF' : OrderedPair (recursionNatVal A a F ha hF i) y ∈ F := by simpa [hxi] using hxyF
      have hStepF : OrderedPair (recursionNatVal A a F ha hF i) (recursionNatVal A a F ha hF (Nat.succ i)) ∈ F :=
        recursionNatVal_step A a F ha hF i
      have hyEq : y = recursionNatVal A a F ha hF (Nat.succ i) :=
        function_value_unique F (recursionNatVal A a F ha hF i) y (recursionNatVal A a F ha hF (Nat.succ i)) hFfun hxyF' hStepF
      have hNext : OrderedPair (n⁺) (recursionNatVal A a F ha hF (Nat.succ i)) ∈ h := by
        have hRaw := recursionGraph_pair_intro A a F ha hF (Nat.succ i)
        simpa [hni, ωCode] using hRaw
      simpa [hyEq] using hNext

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
      exact (hTspec Set.Empty).2 ⟨ω.inductive.left, h0eq⟩
    · intro n hnT
      rcases (hTspec n).1 hnT with ⟨hnω, hIndEq⟩
      have hnSuccω : n⁺ ∈ ω := ω.inductive.right n hnω
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
    have hnDom₁ : n ∈ dom h₁ := Pair.mem_dom h₁ n x hw₁
    have hnω : n ∈ ω := by simpa [h₁Dom] using hnDom₁
    have hnDom₂ : n ∈ dom h₂ := by simpa [h₂Dom] using hnω
    rcases h₂Fun.2 n hnDom₂ with ⟨y, hy, _⟩
    have hxy : x = y := hAgree n hnω x y hw₁ hy
    simpa [hxy] using hy
  · intro hw₂
    rcases h₂Fun.1 w hw₂ with ⟨n, y, hwEq₂⟩
    subst hwEq₂
    have hnDom₂ : n ∈ dom h₂ := Pair.mem_dom h₂ n y hw₂
    have hnω : n ∈ ω := by simpa [h₂Dom] using hnDom₂
    have hnDom₁ : n ∈ dom h₁ := by simpa [h₁Dom] using hnω
    rcases h₁Fun.2 n hnDom₁ with ⟨x, hx, _⟩
    have hxy : x = y := hAgree n hnω x y hx hw₂
    simpa [hxy] using hx

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
  ⟨Set.Empty, e⟩ ∈ f ∧
  (∀ n x y, n ∈ ω → ⟨n, x⟩ ∈ f → (⟨n⁺, y⟩ ∈ f ↔ y = S x))

theorem theorem_4H_peano_isomorphic
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
  have hRanSub : SubsetOf (Relation.Range h) N := hInto.2.2
  have heRan : e ∈ Relation.Range h := (Relation.Range.Spec).2 ⟨Set.Empty, hBase⟩
  have hRanClosed : ∀ x, x ∈ Relation.Range h → S x ∈ Relation.Range h := by
    intro x hxRan
    rcases (Relation.Range.Spec).1 hxRan with ⟨n, hnx⟩
    have hnDom : n ∈ dom h := Pair.mem_dom h n x hnx
    have hnω : n ∈ ω := by simpa [hInto.2.1] using hnDom
    have hxN : x ∈ N := hRanSub x hxRan
    have hxGraph : OrderedPair x (S x) ∈ F := by
      have hG : OrderedPair x (S x) ∈ GraphOn N S :=
        (GraphOn.Pair.Spec hSClosed).2 ⟨hxN, rfl⟩
      simpa [F] using hG
    have hNext : OrderedPair (n⁺) (S x) ∈ h := (hRec n x (S x) hnω hnx).2 hxGraph
    exact (Relation.Range.Spec).2 ⟨n⁺, hNext⟩
  have hRanEq : Relation.Range h = N := hInd (Relation.Range h) hRanSub heRan hRanClosed
  have hOnto : MapsOnto h ω N := ⟨hInto, hRanEq⟩
  refine ⟨h, ?_⟩
  refine ⟨hOnto, hBase, ?_⟩
  intro n x y hnω hnx
  have hxRan : x ∈ Relation.Range h := Pair.mem_ran h n x hnx
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

noncomputable def OmegaSuccessorGraph : Set :=
  GraphOn ω (fun n => n⁺)

theorem ω_successor_graph_maps_into : MapsInto OmegaSuccessorGraph ω ω := by
  unfold OmegaSuccessorGraph
  apply GraphOn.mapsInto
  intro n hnω
  exact ω.inductive.right n hnω

theorem recursion_theorem_on_ω_successor (a : Set) :
    a ∈ ω → ∃! h, RecursionSolution h ω a OmegaSuccessorGraph := by
  intro haω
  exact recursion_theorem_on_ω ω a OmegaSuccessorGraph haω ω_successor_graph_maps_into

end Set
