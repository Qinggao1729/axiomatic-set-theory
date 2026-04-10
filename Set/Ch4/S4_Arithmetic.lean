import Set.Ch4.S3_RecursionOnOmega
import Set.Ch3.S4_Functions

/-!
# Chapter 4, Section 4: Arithmetic

This section formalizes recursive definitions of addition/multiplication/
exponentiation on `ω` and the arithmetic theorem chain (4I/4J/4K), together
with reusable induction and closure lemmas.
-/

namespace Set

def IsBinaryOperationOn (A op : Set) : Prop :=
  MapsInto op (A ⨯ A) A

noncomputable def zero_ω : Set := Set.Empty
noncomputable def one_ω : Set := zero_ω⁺

lemma zero_ω_mem_ω : zero_ω ∈ ω := by
  change Set.Empty ∈ ω
  exact ω.inductive.left

noncomputable def NatAddRel (m : Set) (hmω : m ∈ ω) : Set :=
  Classical.choose (ExistsUnique.exists (recursion_theorem_on_ω_successor m hmω))

lemma NatAddRel.solution (m : Set) (hmω : m ∈ ω) :
    RecursionSolution (NatAddRel m hmω) ω m OmegaSuccessorGraph := by
  exact Classical.choose_spec (ExistsUnique.exists (recursion_theorem_on_ω_successor m hmω))

lemma ω_successor_graph_pair (x y : Set) :
    OrderedPair x y ∈ OmegaSuccessorGraph ↔ x ∈ ω ∧ y = x⁺ := by
  unfold OmegaSuccessorGraph
  exact GraphOn.Pair.Spec (fun n hnω => ω.inductive.right n hnω)

lemma nat_add_rel_zero (m : Set) (hmω : m ∈ ω) :
    OrderedPair zero_ω m ∈ NatAddRel m hmω := by
  exact (NatAddRel.solution m hmω).2.1

lemma nat_add_rel_step (m n x y : Set) (hmω : m ∈ ω) :
    n ∈ ω →
    OrderedPair n x ∈ NatAddRel m hmω →
    (OrderedPair (n⁺) y ∈ NatAddRel m hmω ↔ OrderedPair x y ∈ OmegaSuccessorGraph) := by
  intro hnω hnx
  exact (NatAddRel.solution m hmω).2.2 n x y hnω hnx

lemma nat_add_rel_value_exists_unique (m n : Set) (hmω : m ∈ ω) (hnω : n ∈ ω) :
    ∃! y, OrderedPair n y ∈ NatAddRel m hmω := by
  rcases (NatAddRel.solution m hmω).1 with ⟨hFun, hDom, _⟩
  have hnDom : n ∈ dom (NatAddRel m hmω) := by simpa [hDom] using hnω
  exact hFun.2 n hnDom

noncomputable def NatAdd (m n : Set) : Set :=
  letI : Decidable (m ∈ ω) := Classical.decPred (fun x : Set => x ∈ ω) m
  letI : Decidable (n ∈ ω) := Classical.decPred (fun x : Set => x ∈ ω) n
  if hmω : m ∈ ω then
    if hnω : n ∈ ω then
      Classical.choose (ExistsUnique.exists (nat_add_rel_value_exists_unique m n hmω hnω))
    else Set.Empty
  else Set.Empty

noncomputable instance : HAdd Set Set Set := ⟨NatAdd⟩

lemma nat_add_spec (m n : Set) (hmω : m ∈ ω) (hnω : n ∈ ω) :
    OrderedPair n (m + n) ∈ NatAddRel m hmω := by
  change OrderedPair n (NatAdd m n) ∈ NatAddRel m hmω
  simp [NatAdd, hmω, hnω]
  exact Classical.choose_spec (ExistsUnique.exists (nat_add_rel_value_exists_unique m n hmω hnω))

theorem nat_add_closed (m n : Set) : m ∈ ω → n ∈ ω → m + n ∈ ω := by
  intro hmω hnω
  rcases (NatAddRel.solution m hmω).1 with ⟨_, _, hRanSub⟩
  have hInRan : m + n ∈ ran (NatAddRel m hmω) := by
    exact (Relation.Range.Spec).2 ⟨n, nat_add_spec m n hmω hnω⟩
  exact hRanSub (m + n) hInRan

theorem nat_add_zero (m : Set) : m ∈ ω → m + zero_ω = m := by
  intro hmω
  have h0ω : zero_ω ∈ ω := zero_ω_mem_ω
  have hPairAdd : OrderedPair zero_ω (m + zero_ω) ∈ NatAddRel m hmω :=
    nat_add_spec m zero_ω hmω h0ω
  have hPairZero : OrderedPair zero_ω m ∈ NatAddRel m hmω :=
    nat_add_rel_zero m hmω
  have hFun : IsFunction (NatAddRel m hmω) := (NatAddRel.solution m hmω).1.1
  exact function_value_unique (NatAddRel m hmω) zero_ω (m + zero_ω) m hFun hPairAdd hPairZero

theorem nat_add_succ (m n : Set) : m ∈ ω → n ∈ ω → m + n⁺ = (m + n)⁺ := by
  intro hmω hnω
  have hnSuccω : n⁺ ∈ ω := ω.inductive.right n hnω
  have hPairN : OrderedPair n (m + n) ∈ NatAddRel m hmω :=
    nat_add_spec m n hmω hnω
  have hGraph : OrderedPair (m + n) ((m + n)⁺) ∈ OmegaSuccessorGraph := by
    exact (ω_successor_graph_pair (m + n) ((m + n)⁺)).2 ⟨nat_add_closed m n hmω hnω, rfl⟩
  have hPairSuccStep : OrderedPair (n⁺) ((m + n)⁺) ∈ NatAddRel m hmω := by
    exact (nat_add_rel_step m n (m + n) ((m + n)⁺) hmω hnω hPairN).2 hGraph
  have hPairSuccVal : OrderedPair (n⁺) (m + n⁺) ∈ NatAddRel m hmω :=
    nat_add_spec m (n⁺) hmω hnSuccω
  have hFun : IsFunction (NatAddRel m hmω) := (NatAddRel.solution m hmω).1.1
  exact function_value_unique (NatAddRel m hmω) (n⁺) (m + n⁺) ((m + n)⁺) hFun hPairSuccVal hPairSuccStep

noncomputable def OmegaAddRightGraph (m : Set) : Set :=
  GraphOn ω (fun x => x + m)

theorem ω_add_right_graph_maps_into (m : Set) :
    m ∈ ω → MapsInto (OmegaAddRightGraph m) ω ω := by
  intro hmω
  unfold OmegaAddRightGraph
  apply GraphOn.mapsInto
  intro x hxω
  exact nat_add_closed x m hxω hmω

theorem recursion_theorem_on_ω_add_right (m : Set) :
    m ∈ ω → ∃! h, RecursionSolution h ω zero_ω (OmegaAddRightGraph m) := by
  intro hmω
  apply recursion_theorem_on_ω ω zero_ω (OmegaAddRightGraph m)
  · exact zero_ω_mem_ω
  · exact ω_add_right_graph_maps_into m hmω

noncomputable def NatMulRel (m : Set) (hmω : m ∈ ω) : Set :=
  Classical.choose (ExistsUnique.exists (recursion_theorem_on_ω_add_right m hmω))

lemma NatMulRel.solution (m : Set) (hmω : m ∈ ω) :
    RecursionSolution (NatMulRel m hmω) ω zero_ω (OmegaAddRightGraph m) := by
  exact Classical.choose_spec (ExistsUnique.exists (recursion_theorem_on_ω_add_right m hmω))

lemma ω_add_right_graph_pair (m x y : Set) (hmω : m ∈ ω) :
    OrderedPair x y ∈ OmegaAddRightGraph m ↔ x ∈ ω ∧ y = x + m := by
  unfold OmegaAddRightGraph
  exact GraphOn.Pair.Spec (fun t htω => nat_add_closed t m htω hmω)

lemma nat_mul_rel_zero (m : Set) (hmω : m ∈ ω) :
    OrderedPair zero_ω zero_ω ∈ NatMulRel m hmω := by
  exact (NatMulRel.solution m hmω).2.1

lemma nat_mul_rel_step (m n x y : Set) (hmω : m ∈ ω) :
    n ∈ ω →
    OrderedPair n x ∈ NatMulRel m hmω →
    (OrderedPair (n⁺) y ∈ NatMulRel m hmω ↔ OrderedPair x y ∈ OmegaAddRightGraph m) := by
  intro hnω hnx
  exact (NatMulRel.solution m hmω).2.2 n x y hnω hnx

lemma nat_mul_rel_value_exists_unique (m n : Set) (hmω : m ∈ ω) (hnω : n ∈ ω) :
    ∃! y, OrderedPair n y ∈ NatMulRel m hmω := by
  rcases (NatMulRel.solution m hmω).1 with ⟨hFun, hDom, _⟩
  have hnDom : n ∈ dom (NatMulRel m hmω) := by simpa [hDom] using hnω
  exact hFun.2 n hnDom

noncomputable def NatMulCanon (m n : Set) : Set :=
  letI : Decidable (m ∈ ω) := Classical.decPred (fun x : Set => x ∈ ω) m
  letI : Decidable (n ∈ ω) := Classical.decPred (fun x : Set => x ∈ ω) n
  if hmω : m ∈ ω then
    if hnω : n ∈ ω then
      Classical.choose (ExistsUnique.exists (nat_mul_rel_value_exists_unique m n hmω hnω))
    else Set.Empty
  else Set.Empty

lemma nat_mul_canon_spec (m n : Set) (hmω : m ∈ ω) (hnω : n ∈ ω) :
    OrderedPair n (NatMulCanon m n) ∈ NatMulRel m hmω := by
  simp [NatMulCanon, hmω, hnω]
  exact Classical.choose_spec (ExistsUnique.exists (nat_mul_rel_value_exists_unique m n hmω hnω))

theorem nat_mul_canon_closed (m n : Set) :
    m ∈ ω → n ∈ ω → NatMulCanon m n ∈ ω := by
  intro hmω hnω
  rcases (NatMulRel.solution m hmω).1 with ⟨_, _, hRanSub⟩
  have hInRan : NatMulCanon m n ∈ ran (NatMulRel m hmω) := by
    exact (Relation.Range.Spec).2
      ⟨n, nat_mul_canon_spec m n hmω hnω⟩
  exact hRanSub (NatMulCanon m n) hInRan

theorem nat_mul_canon_zero (m : Set) :
    m ∈ ω → NatMulCanon m zero_ω = zero_ω := by
  intro hmω
  have h0ω : zero_ω ∈ ω := zero_ω_mem_ω
  have hPairMul : OrderedPair zero_ω (NatMulCanon m zero_ω) ∈ NatMulRel m hmω :=
    nat_mul_canon_spec m zero_ω hmω h0ω
  have hPairZero : OrderedPair zero_ω zero_ω ∈ NatMulRel m hmω :=
    nat_mul_rel_zero m hmω
  have hFun : IsFunction (NatMulRel m hmω) := (NatMulRel.solution m hmω).1.1
  exact function_value_unique (NatMulRel m hmω) zero_ω (NatMulCanon m zero_ω) zero_ω hFun hPairMul hPairZero

theorem nat_mul_canon_succ (m n : Set) :
    m ∈ ω → n ∈ ω → NatMulCanon m (n⁺) = NatMulCanon m n + m := by
  intro hmω hnω
  have hnSuccω : n⁺ ∈ ω := ω.inductive.right n hnω
  have hPairN : OrderedPair n (NatMulCanon m n) ∈ NatMulRel m hmω :=
    nat_mul_canon_spec m n hmω hnω
  have hGraph : OrderedPair (NatMulCanon m n) ((NatMulCanon m n) + m) ∈ OmegaAddRightGraph m := by
    exact (ω_add_right_graph_pair m (NatMulCanon m n) ((NatMulCanon m n) + m) hmω).2
      ⟨nat_mul_canon_closed m n hmω hnω, rfl⟩
  have hPairSuccStep : OrderedPair (n⁺) ((NatMulCanon m n) + m) ∈ NatMulRel m hmω := by
    exact (nat_mul_rel_step m n (NatMulCanon m n) ((NatMulCanon m n) + m) hmω hnω hPairN).2 hGraph
  have hPairSuccVal : OrderedPair (n⁺) (NatMulCanon m (n⁺)) ∈ NatMulRel m hmω :=
    nat_mul_canon_spec m (n⁺) hmω hnSuccω
  have hFun : IsFunction (NatMulRel m hmω) := (NatMulRel.solution m hmω).1.1
  exact function_value_unique (NatMulRel m hmω) (n⁺) (NatMulCanon m (n⁺)) ((NatMulCanon m n) + m) hFun hPairSuccVal hPairSuccStep

noncomputable def NatMul (m n : Set) : Set := NatMulCanon m n

noncomputable instance : HMul Set Set Set := ⟨NatMul⟩

theorem nat_mul_closed (m n : Set) : m ∈ ω → n ∈ ω → m * n ∈ ω := by
  intro hmω hnω
  change NatMul m n ∈ ω
  simpa [NatMul] using nat_mul_canon_closed m n hmω hnω

theorem nat_mul_zero (m : Set) : m ∈ ω → m * zero_ω = zero_ω := by
  intro hmω
  change NatMul m zero_ω = zero_ω
  simpa [NatMul] using nat_mul_canon_zero m hmω

theorem nat_mul_succ (m n : Set) : m ∈ ω → n ∈ ω → m * n⁺ = (m * n) + m := by
  intro hmω hnω
  change NatMul m (n⁺) = (NatMul m n) + m
  simpa [NatMul] using nat_mul_canon_succ m n hmω hnω

noncomputable def OmegaMulRightGraph (m : Set) : Set :=
  GraphOn ω (fun x => x * m)

theorem ω_mul_right_graph_maps_into (m : Set) :
    m ∈ ω → MapsInto (OmegaMulRightGraph m) ω ω := by
  intro hmω
  unfold OmegaMulRightGraph
  apply GraphOn.mapsInto
  intro x hxω
  exact nat_mul_closed x m hxω hmω

lemma one_ω_mem_ω : one_ω ∈ ω := by
  simpa [one_ω, zero_ω] using ω.inductive.right Set.Empty ω.inductive.left

theorem recursion_theorem_on_ω_mul_right (m : Set) :
    m ∈ ω → ∃! h, RecursionSolution h ω one_ω (OmegaMulRightGraph m) := by
  intro hmω
  apply recursion_theorem_on_ω ω one_ω (OmegaMulRightGraph m)
  · exact one_ω_mem_ω
  · exact ω_mul_right_graph_maps_into m hmω

noncomputable def NatPowRel (m : Set) (hmω : m ∈ ω) : Set :=
  Classical.choose (ExistsUnique.exists (recursion_theorem_on_ω_mul_right m hmω))

lemma NatPowRel.solution (m : Set) (hmω : m ∈ ω) :
    RecursionSolution (NatPowRel m hmω) ω one_ω (OmegaMulRightGraph m) := by
  exact Classical.choose_spec (ExistsUnique.exists (recursion_theorem_on_ω_mul_right m hmω))

lemma ω_mul_right_graph_pair (m x y : Set) (hmω : m ∈ ω) :
    OrderedPair x y ∈ OmegaMulRightGraph m ↔ x ∈ ω ∧ y = x * m := by
  unfold OmegaMulRightGraph
  exact GraphOn.Pair.Spec (fun t htω => nat_mul_closed t m htω hmω)

lemma nat_pow_rel_zero (m : Set) (hmω : m ∈ ω) :
    OrderedPair zero_ω one_ω ∈ NatPowRel m hmω := by
  exact (NatPowRel.solution m hmω).2.1

lemma nat_pow_rel_step (m n x y : Set) (hmω : m ∈ ω) :
    n ∈ ω →
    OrderedPair n x ∈ NatPowRel m hmω →
    (OrderedPair (n⁺) y ∈ NatPowRel m hmω ↔ OrderedPair x y ∈ OmegaMulRightGraph m) := by
  intro hnω hnx
  exact (NatPowRel.solution m hmω).2.2 n x y hnω hnx

lemma nat_pow_rel_value_exists_unique (m n : Set) (hmω : m ∈ ω) (hnω : n ∈ ω) :
    ∃! y, OrderedPair n y ∈ NatPowRel m hmω := by
  rcases (NatPowRel.solution m hmω).1 with ⟨hFun, hDom, _⟩
  have hnDom : n ∈ dom (NatPowRel m hmω) := by simpa [hDom] using hnω
  exact hFun.2 n hnDom

noncomputable def NatPowCanon (m n : Set) : Set :=
  letI : Decidable (m ∈ ω) := Classical.decPred (fun x : Set => x ∈ ω) m
  letI : Decidable (n ∈ ω) := Classical.decPred (fun x : Set => x ∈ ω) n
  if hmω : m ∈ ω then
    if hnω : n ∈ ω then
      Classical.choose (ExistsUnique.exists (nat_pow_rel_value_exists_unique m n hmω hnω))
    else Set.Empty
  else Set.Empty

lemma nat_pow_canon_spec (m n : Set) (hmω : m ∈ ω) (hnω : n ∈ ω) :
    OrderedPair n (NatPowCanon m n) ∈ NatPowRel m hmω := by
  simp [NatPowCanon, hmω, hnω]
  exact Classical.choose_spec (ExistsUnique.exists (nat_pow_rel_value_exists_unique m n hmω hnω))

theorem nat_pow_canon_closed (m n : Set) :
    m ∈ ω → n ∈ ω → NatPowCanon m n ∈ ω := by
  intro hmω hnω
  rcases (NatPowRel.solution m hmω).1 with ⟨_, _, hRanSub⟩
  have hInRan : NatPowCanon m n ∈ ran (NatPowRel m hmω) := by
    exact (Relation.Range.Spec).2
      ⟨n, nat_pow_canon_spec m n hmω hnω⟩
  exact hRanSub (NatPowCanon m n) hInRan

theorem nat_pow_canon_zero (m : Set) :
    m ∈ ω → NatPowCanon m zero_ω = one_ω := by
  intro hmω
  have h0ω : zero_ω ∈ ω := zero_ω_mem_ω
  have hPairPow : OrderedPair zero_ω (NatPowCanon m zero_ω) ∈ NatPowRel m hmω :=
    nat_pow_canon_spec m zero_ω hmω h0ω
  have hPairZero : OrderedPair zero_ω one_ω ∈ NatPowRel m hmω :=
    nat_pow_rel_zero m hmω
  have hFun : IsFunction (NatPowRel m hmω) := (NatPowRel.solution m hmω).1.1
  exact function_value_unique (NatPowRel m hmω) zero_ω (NatPowCanon m zero_ω) one_ω hFun hPairPow hPairZero

theorem nat_pow_canon_succ (m n : Set) :
    m ∈ ω → n ∈ ω → NatPowCanon m (n⁺) = (NatPowCanon m n) * m := by
  intro hmω hnω
  have hnSuccω : n⁺ ∈ ω := ω.inductive.right n hnω
  have hPairN : OrderedPair n (NatPowCanon m n) ∈ NatPowRel m hmω :=
    nat_pow_canon_spec m n hmω hnω
  have hGraph : OrderedPair (NatPowCanon m n) ((NatPowCanon m n) * m) ∈ OmegaMulRightGraph m := by
    exact (ω_mul_right_graph_pair m (NatPowCanon m n) ((NatPowCanon m n) * m) hmω).2
      ⟨nat_pow_canon_closed m n hmω hnω, rfl⟩
  have hPairSuccStep : OrderedPair (n⁺) ((NatPowCanon m n) * m) ∈ NatPowRel m hmω := by
    exact (nat_pow_rel_step m n (NatPowCanon m n) ((NatPowCanon m n) * m) hmω hnω hPairN).2 hGraph
  have hPairSuccVal : OrderedPair (n⁺) (NatPowCanon m (n⁺)) ∈ NatPowRel m hmω :=
    nat_pow_canon_spec m (n⁺) hmω hnSuccω
  have hFun : IsFunction (NatPowRel m hmω) := (NatPowRel.solution m hmω).1.1
  exact function_value_unique (NatPowRel m hmω) (n⁺) (NatPowCanon m (n⁺)) ((NatPowCanon m n) * m) hFun hPairSuccVal hPairSuccStep

noncomputable def NatPow (m n : Set) : Set := NatPowCanon m n

noncomputable instance : Pow Set Set := ⟨NatPow⟩

theorem nat_pow_closed (m n : Set) : m ∈ ω → n ∈ ω → m ^ n ∈ ω := by
  intro hmω hnω
  change NatPow m n ∈ ω
  simpa [NatPow] using nat_pow_canon_closed m n hmω hnω

theorem nat_pow_zero (m : Set) : m ∈ ω → m ^ zero_ω = one_ω := by
  intro hmω
  change NatPow m zero_ω = one_ω
  simpa [NatPow] using nat_pow_canon_zero m hmω

theorem nat_pow_succ (m n : Set) : m ∈ ω → n ∈ ω → m ^ (n⁺) = (m ^ n) * m := by
  intro hmω hnω
  change NatPow m (n⁺) = (NatPow m n) * m
  simpa [NatPow] using nat_pow_canon_succ m n hmω hnω

theorem nat_zero_add (n : Set) :
    n ∈ ω → zero_ω + n = n := by
  intro hnω
  apply ω_induction (fun k => zero_ω + k = k)
  · change zero_ω + zero_ω = zero_ω
    exact nat_add_zero zero_ω zero_ω_mem_ω
  · intro k hkω hEq0k
    calc
      zero_ω + k⁺ = (zero_ω + k)⁺ := nat_add_succ zero_ω k zero_ω_mem_ω hkω
      _ = k⁺ := by simp [hEq0k]
  · exact hnω

theorem nat_succ_add (m n : Set) :
    m ∈ ω → n ∈ ω → m⁺ + n = (m + n)⁺ := by
  intro hmω hnω
  have hmSuccω : m⁺ ∈ ω := ω.inductive.right m hmω
  apply ω_induction (fun k => m⁺ + k = (m + k)⁺)
  · change m⁺ + zero_ω = (m + zero_ω)⁺
    calc
      m⁺ + zero_ω = m⁺ := nat_add_zero (m⁺) hmSuccω
      _ = (m + zero_ω)⁺ := by rw [nat_add_zero m hmω]
  · intro k hkω hIh
    calc
      m⁺ + k⁺ = (m⁺ + k)⁺ := nat_add_succ (m⁺) k hmSuccω hkω
      _ = ((m + k)⁺)⁺ := by simp [hIh]
      _ = (m + k⁺)⁺ := by simp [nat_add_succ m k hmω hkω]
  · exact hnω

theorem nat_add_comm (a b : Set) :
  a ∈ ω → b ∈ ω → a + b = b + a := by
  intro haω hbω
  apply ω_induction (fun k => a + k = k + a)
  · change a + zero_ω = zero_ω + a
    calc
      a + zero_ω = a := nat_add_zero a haω
      _ = zero_ω + a := (nat_zero_add a haω).symm
  · intro k hkω hIh
    calc
      a + k⁺ = (a + k)⁺ := nat_add_succ a k haω hkω
      _ = (k + a)⁺ := by simp [hIh]
      _ = k⁺ + a := (nat_succ_add k a hkω haω).symm
  · exact hbω

theorem nat_add_assoc (a b c : Set) :
  a ∈ ω → b ∈ ω → c ∈ ω → (a + b) + c = a + (b + c) := by
  intro haω hbω hcω
  have habω : a + b ∈ ω := nat_add_closed a b haω hbω
  apply ω_induction (fun k => (a + b) + k = a + (b + k))
  · change (a + b) + zero_ω = a + (b + zero_ω)
    calc
      (a + b) + zero_ω = a + b := nat_add_zero (a + b) habω
      _ = a + (b + zero_ω) := by rw [nat_add_zero b hbω]
  · intro k hkω hIh
    have hbkω : b + k ∈ ω := nat_add_closed b k hbω hkω
    calc
      (a + b) + k⁺ = ((a + b) + k)⁺ := nat_add_succ (a + b) k habω hkω
      _ = (a + (b + k))⁺ := by simp [hIh]
      _ = a + (b + k⁺) := by
        simpa [nat_add_succ b k hbω hkω] using (nat_add_succ a (b + k) haω hbkω).symm
  · exact hcω
theorem nat_left_distrib (a b c : Set) :
  a ∈ ω → b ∈ ω → c ∈ ω → a * (b + c) = (a * b) + (a * c) := by
  intro haω hbω hcω
  have habmulω : a * b ∈ ω := nat_mul_closed a b haω hbω
  apply ω_induction (fun k => a * (b + k) = (a * b) + (a * k))
  · change a * (b + zero_ω) = (a * b) + (a * zero_ω)
    calc
      a * (b + zero_ω) = a * b := by rw [nat_add_zero b hbω]
      _ = (a * b) + zero_ω := (nat_add_zero (a * b) habmulω).symm
      _ = (a * b) + (a * zero_ω) := by rw [nat_mul_zero a haω]
  · intro k hkω hIh
    have hbkω : b + k ∈ ω := nat_add_closed b k hbω hkω
    have hakω : a * k ∈ ω := nat_mul_closed a k haω hkω
    calc
      a * (b + k⁺) = a * ((b + k)⁺) := by simp [nat_add_succ b k hbω hkω]
      _ = (a * (b + k)) + a := nat_mul_succ a (b + k) haω hbkω
      _ = (((a * b) + (a * k)) + a) := by simp [hIh]
      _ = ((a * b) + ((a * k) + a)) := nat_add_assoc (a * b) (a * k) a habmulω hakω haω
      _ = (a * b) + (a * k⁺) := by simp [nat_mul_succ a k haω hkω]
  · exact hcω

theorem nat_mul_assoc (a b c : Set) :
  a ∈ ω → b ∈ ω → c ∈ ω → (a * b) * c = a * (b * c) := by
  intro haω hbω hcω
  have habω : a * b ∈ ω := nat_mul_closed a b haω hbω
  apply ω_induction (fun k => (a * b) * k = a * (b * k)) 
  · change (a * b) * zero_ω = a * (b * zero_ω)
    calc
      (a * b) * zero_ω = zero_ω := nat_mul_zero (a * b) habω
      _ = a * zero_ω := (nat_mul_zero a haω).symm
      _ = a * (b * zero_ω) := by rw [nat_mul_zero b hbω]
  · intro k hkω hIh
    have hbkω : b * k ∈ ω := nat_mul_closed b k hbω hkω
    calc
      (a * b) * k⁺ = ((a * b) * k) + (a * b) := nat_mul_succ (a * b) k habω hkω
      _ = (a * (b * k)) + (a * b) := by simp [hIh]
      _ = a * ((b * k) + b) := (nat_left_distrib a (b * k) b haω hbkω hbω).symm
      _ = a * (b * k⁺) := by simp [nat_mul_succ b k hbω hkω]
  · exact hcω

theorem nat_zero_mul (n : Set) :
    n ∈ ω → zero_ω * n = zero_ω := by
  intro hnω
  apply ω_induction (fun k => zero_ω * k = zero_ω)
  · change zero_ω * zero_ω = zero_ω
    exact nat_mul_zero zero_ω zero_ω_mem_ω
  · intro k hkω hIh
    calc
      zero_ω * k⁺ = (zero_ω * k) + zero_ω := nat_mul_succ zero_ω k zero_ω_mem_ω hkω
      _ = zero_ω + zero_ω := by simp [hIh]
      _ = zero_ω := nat_add_zero zero_ω zero_ω_mem_ω
  · exact hnω

theorem nat_mul_succ_left (m n : Set) :
    m ∈ ω → n ∈ ω → m⁺ * n = (m * n) + n := by
  intro hmω hnω
  have hmSuccω : m⁺ ∈ ω := ω.inductive.right m hmω
  apply ω_induction (fun k => m⁺ * k = (m * k) + k)
  · change m⁺ * zero_ω = (m * zero_ω) + zero_ω
    have hm0ω : m * zero_ω ∈ ω := nat_mul_closed m zero_ω hmω zero_ω_mem_ω
    calc
      m⁺ * zero_ω = zero_ω := nat_mul_zero (m⁺) hmSuccω
      _ = (m * zero_ω) + zero_ω := by
        rw [nat_mul_zero m hmω]
        exact (nat_add_zero zero_ω zero_ω_mem_ω).symm
  · intro k hkω hIh
    have hmkω : m * k ∈ ω := nat_mul_closed m k hmω hkω
    have hmkAddkω : (m * k) + k ∈ ω := nat_add_closed (m * k) k hmkω hkω
    have hmksuccω : m * k⁺ ∈ ω := nat_mul_closed m (k⁺) hmω (ω.inductive.right k hkω)
    calc
      m⁺ * k⁺ = (m⁺ * k) + m⁺ := nat_mul_succ (m⁺) k hmSuccω hkω
      _ = ((m * k) + k) + m⁺ := by simp [hIh]
      _ = (((m * k) + k) + m)⁺ := nat_add_succ ((m * k) + k) m hmkAddkω hmω
      _ = ((((m * k) + m) + k))⁺ := by
        rw [nat_add_assoc (m * k) k m hmkω hkω hmω]
        rw [nat_add_comm k m hkω hmω]
        rw [(nat_add_assoc (m * k) m k hmkω hmω hkω).symm]
      _ = (m * k⁺ + k)⁺ := by simp [nat_mul_succ m k hmω hkω]
      _ = (m * k⁺) + k⁺ := (nat_add_succ (m * k⁺) k hmksuccω hkω).symm
  · exact hnω

theorem nat_mul_comm (a b : Set) :
  a ∈ ω → b ∈ ω → a * b = b * a := by
  intro haω hbω
  apply ω_induction (fun k => a * k = k * a)
  · change a * zero_ω = zero_ω * a
    calc
      a * zero_ω = zero_ω := nat_mul_zero a haω
      _ = zero_ω * a := (nat_zero_mul a haω).symm
  · intro k hkω hIh
    calc
      a * k⁺ = (a * k) + a := nat_mul_succ a k haω hkω
      _ = (k * a) + a := by simp [hIh]
      _ = k⁺ * a := (nat_mul_succ_left k a hkω haω).symm
  · exact hbω
theorem nat_right_distrib (a b c : Set) :
  a ∈ ω → b ∈ ω → c ∈ ω → (a + b) * c = (a * c) + (b * c) := by
  intro ha hb hc
  calc
    (a + b) * c = c * (a + b) := nat_mul_comm (a + b) c (nat_add_closed a b ha hb) hc
    _ = (c * a) + (c * b) := nat_left_distrib c a b hc ha hb
    _ = (a * c) + (c * b) := by rw [nat_mul_comm c a hc ha]
    _ = (a * c) + (b * c) := by rw [nat_mul_comm c b hc hb]

theorem theorem_4K_basic_arithmetic_laws :
    (∀ a b c, a ∈ ω → b ∈ ω → c ∈ ω → (a + b) + c = a + (b + c)) ∧
    (∀ a b, a ∈ ω → b ∈ ω → a + b = b + a) ∧
    (∀ a b c, a ∈ ω → b ∈ ω → c ∈ ω → (a * b) * c = a * (b * c)) ∧
    (∀ a b, a ∈ ω → b ∈ ω → a * b = b * a) ∧
    (∀ a b c, a ∈ ω → b ∈ ω → c ∈ ω → a * (b + c) = (a * b) + (a * c)) := by
  refine ⟨nat_add_assoc, nat_add_comm, nat_mul_assoc, nat_mul_comm, nat_left_distrib⟩

end Set
