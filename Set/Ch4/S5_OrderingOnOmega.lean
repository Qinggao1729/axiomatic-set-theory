import Set.Ch4.S4_Arithmetic

/-!
# Chapter 4, Section 5: Ordering on ω

This section formalizes ordering results on `ω` (4L/4M/4N/4P), including
trichotomy-style comparisons, well-ordering consequences, and strong induction.
-/

namespace Set

def NatLt (m n : Set) : Prop := m ∈ n
def NatLe (m n : Set) : Prop := m ∈ n ∨ m = n

/- [Enderton, Lemma 4L(a), pp.83-84] -/
theorem thm_4L_a_natural_succ_mem_iff (m n : Set) :
    m ∈ ω → n ∈ ω → (m ∈ n ↔ m⁺ ∈ n⁺) := by
  intro hmω hnω
  apply Iff.intro
  · intro hmn
    exact succ_mem_succ_of_mem m n hnω hmn
  · intro hSucc
    have hmInSucc : m ∈ m⁺ := (mem_successor_iff m m).2 (Or.inr rfl)
    rcases (mem_successor_iff (m⁺) n).1 hSucc with hSuccInN | hEq
    · have hnTrans : IsTransitiveSet n := natural_transitive_set n ((ω.Spec).1 hnω)
      exact hnTrans _ _ hmInSucc hSuccInN
    · exact by simpa [hEq] using hmInSucc

abbrev natural_succ_mem_iff := thm_4L_a_natural_succ_mem_iff

/- [Enderton, Lemma 4L(b), pp.83-84] -/
theorem thm_4L_b_natural_not_mem_self (n : Set) : n ∈ ω → n ∉ n := by
  intro hnω
  exact natural_not_mem_self n hnω

abbrev natural_not_mem_self_4L := thm_4L_b_natural_not_mem_self

/- [Enderton, Lemma 4L(a), pp.83-84] -/
theorem thm_4L_a_natural_mem_implies_subset (m n : Set) :
    m ∈ ω → n ∈ ω → m ∈ n → m ⊆ n := by
  intro hmω hnω hmn
  have hnTrans : IsTransitiveSet n := natural_transitive_set n ((ω.Spec).1 hnω)
  intro x hx
  exact hnTrans x m hx hmn

abbrev natural_mem_implies_subset := thm_4L_a_natural_mem_implies_subset

/- [Enderton, Lemma 4L(b) consequence, pp.83-84] -/
theorem thm_4L_b_consequence_natural_mem_implies_ne (m n : Set) :
    m ∈ ω → n ∈ ω → m ∈ n → m ≠ n := by
  intro hmω hnω hmn hEq
  have hmNot : m ∉ m := natural_not_mem_self_4L m hmω
  have hmInm : m ∈ m := by simpa [hEq] using hmn
  exact hmNot hmInm

/- [Enderton, helper for Trichotomy on ω, p.84] -/
theorem natural_zero_eq_or_mem (m : Set) : m ∈ ω → (m = Set.Empty ∨ Set.Empty ∈ m) := by
  intro hmω
  apply ω_induction (fun k => k = Set.Empty ∨ Set.Empty ∈ k)
  · exact Or.inl rfl
  · intro k _ hkProp
    have h0InKSucc : Set.Empty ∈ k⁺ := by
      cases hkProp with
      | inl hkEq =>
        exact (mem_successor_iff Set.Empty k).2 (Or.inr hkEq.symm)
      | inr h0InK =>
        exact (mem_successor_iff Set.Empty k).2 (Or.inl h0InK)
    exact Or.inr h0InKSucc
  · exact hmω

/- [Enderton, Trichotomy preparation on ω, p.84] -/
theorem natural_compare (m n : Set) :
    m ∈ ω → n ∈ ω → (m ∈ n ∨ m = n ∨ n ∈ m) := by
  intro hmω hnω
  have hAll : ∀ k, k ∈ ω → (∀ t, t ∈ ω → (t ∈ k ∨ t = k ∨ k ∈ t)) := by
    apply ω_induction (fun k => ∀ t, t ∈ ω → (t ∈ k ∨ t = k ∨ k ∈ t))
    · intro t htω
      rcases natural_zero_eq_or_mem t htω with htEq | h0t
      · exact Or.inr (Or.inl htEq)
      · exact Or.inr (Or.inr h0t)
    · intro k hkω hkProp t htω
      rcases hkProp t htω with htk | htk | hkt
      · exact Or.inl ((mem_successor_iff t k).2 (Or.inl htk))
      · exact Or.inl ((mem_successor_iff t k).2 (Or.inr htk))
      · have hSucc : k⁺ ∈ t⁺ := (natural_succ_mem_iff k t hkω htω).1 hkt
        rcases (mem_successor_iff (k⁺) t).1 hSucc with hkSuccInT | hkSuccEqT
        · exact Or.inr (Or.inr hkSuccInT)
        · exact Or.inr (Or.inl hkSuccEqT.symm)
  exact hAll n hnω m hmω

/- [Enderton, Trichotomy Law for ω, p.84] -/
theorem natural_trichotomy (m n : Set) :
    m ∈ ω → n ∈ ω →
    (m ∈ n ∨ m = n ∨ n ∈ m) ∧
    ¬(m ∈ n ∧ m = n) ∧
    ¬(m ∈ n ∧ n ∈ m) ∧
    ¬(m = n ∧ n ∈ m) := by
  intro hmω hnω
  refine ⟨natural_compare m n hmω hnω, ?_, ?_, ?_⟩
  · intro h
    rcases h with ⟨hmn, hEq⟩
    have hmNot : m ∉ m := natural_not_mem_self_4L m hmω
    have hmInm : m ∈ m := by simpa [hEq] using hmn
    exact hmNot hmInm
  · intro h
    rcases h with ⟨hmn, hnm⟩
    have hmNot : m ∉ m := natural_not_mem_self_4L m hmω
    have hmTrans : IsTransitiveSet m := natural_transitive_set m ((ω.Spec).1 hmω)
    have hmInm : m ∈ m := hmTrans m n hmn hnm
    exact hmNot hmInm
  · intro h
    rcases h with ⟨hEq, hnm⟩
    have hnNot : n ∉ n := natural_not_mem_self_4L n hnω
    have hnInn : n ∈ n := by simpa [hEq] using hnm
    exact hnNot hnInn

abbrev natural_mem_implies_ne := thm_4L_b_consequence_natural_mem_implies_ne

/- [Enderton, Corollary 4M (membership vs proper subset), p.84] -/
theorem cor_4M_mem_iff_proper_subset (m n : Set) :
    m ∈ ω → n ∈ ω → (m ∈ n ↔ m ⊆ n ∧ m ≠ n) := by
  intro hmω hnω
  apply Iff.intro
  · intro hmn
    exact ⟨natural_mem_implies_subset m n hmω hnω hmn, natural_mem_implies_ne m n hmω hnω hmn⟩
  · intro h
    rcases h with ⟨hSub, hNe⟩
    rcases natural_compare m n hmω hnω with hmn | hEq | hnm
    · exact hmn
    · exfalso
      exact hNe hEq
    · exfalso
      have hnNot : n ∉ n := natural_not_mem_self_4L n hnω
      exact hnNot (hSub n hnm)

abbrev natural_mem_iff_proper_subset := cor_4M_mem_iff_proper_subset

/- [Enderton, Corollary 4M (≤ vs subset), p.84] -/
theorem cor_4M_le_iff_subset (m n : Set) :
    m ∈ ω → n ∈ ω → ((m ∈ n ∨ m = n) ↔ m ⊆ n) := by
  intro hmω hnω
  apply Iff.intro
  · intro h
    cases h with
    | inl hmn =>
      exact natural_mem_implies_subset m n hmω hnω hmn
    | inr hEq =>
      intro x hx
      simpa [hEq] using hx
  · intro hSub
    rcases natural_compare m n hmω hnω with hmn | hEq | hnm
    · exact Or.inl hmn
    · exact Or.inr hEq
    · exfalso
      have hnNot : n ∉ n := natural_not_mem_self_4L n hnω
      exact hnNot (hSub n hnm)

/- [Enderton, Well-ordering of ω, pp.86-87] -/
theorem omega_well_ordering (A : Set) :
    A ⊆ ω → A.Nonempty → ∃ m, m ∈ A ∧ ∀ n, n ∈ A → (m ∈ n ∨ m = n) := by
  intro hAω hANe
  by_contra hNoLeast
  have hNoLeast' : ∀ k, k ∈ A → ∃ t, t ∈ A ∧ t ∈ k := by
    intro k hkA
    by_contra hNoSmall
    have hkω : k ∈ ω := hAω k hkA
    have hLeastK : ∀ n, n ∈ A → (k ∈ n ∨ k = n) := by
      intro n hnA
      have hnω : n ∈ ω := hAω n hnA
      rcases natural_compare n k hnω hkω with hnk | hEq | hkn
      · exfalso
        exact hNoSmall ⟨n, hnA, hnk⟩
      · exact Or.inr hEq.symm
      · exact Or.inl hkn
    exact hNoLeast ⟨k, hkA, hLeastK⟩
  have hAllNotA : ∀ k, k ∈ ω → ∀ n, n ∈ k → n ∉ A := by
    apply ω_induction (fun k => ∀ n, n ∈ k → n ∉ A)
    · intro n hn
      exact (Empty.Spec hn).elim
    · intro k hkω hkProp n hn
      rcases (mem_successor_iff n k).1 hn with hnk | hEq
      · exact hkProp n hnk
      · intro hkA
        have hkA' : k ∈ A := by simpa [hEq] using hkA
        rcases hNoLeast' k hkA' with ⟨t, htA, htk⟩
        exact (hkProp t htk) htA
  rcases hANe with ⟨a, haA⟩
  have haω : a ∈ ω := hAω a haA
  have haSuccω : a⁺ ∈ ω := thm_4B_ω_inductive.right a haω
  have hNotA : a ∉ A := by
    have haInSucc : a ∈ a⁺ := (mem_successor_iff a a).2 (Or.inr rfl)
    exact hAllNotA (a⁺) haSuccω a haInSucc
  exact hNotA haA

/- [Enderton, Strong induction principle on ω, p.88] -/
theorem strong_induction_omega (A : Set) :
    (∀ n, n ∈ ω → (∀ m, m ∈ n → m ∈ A) → n ∈ A) → ω ⊆ A := by
  intro hStep
  intro n hnω
  by_contra hnA
  let C : Set := ω - A
  have hCsub : C ⊆ ω := by
    intro x hx
    exact (Difference.Spec.1 hx).left
  have hCne : C.Nonempty := by
    refine ⟨n, ?_⟩
    exact Difference.Spec.2 ⟨hnω, hnA⟩
  rcases omega_well_ordering C hCsub hCne with ⟨c, hcC, hcLeast⟩
  have hcω : c ∈ ω := (Difference.Spec.1 hcC).left
  have hcNotA : c ∉ A := (Difference.Spec.1 hcC).right
  have hAllSmallA : ∀ m, m ∈ c → m ∈ A := by
    intro m hmc
    have hmω : m ∈ ω := ω_transitive_set m c hmc hcω
    by_contra hmNotA
    have hmC : m ∈ C := Difference.Spec.2 ⟨hmω, hmNotA⟩
    rcases hcLeast m hmC with hcm | hEq
    · have hmTrans : IsTransitiveSet m := natural_transitive_set m ((ω.Spec).1 hmω)
      have hmInm : m ∈ m := hmTrans m c hmc hcm
      exact (natural_not_mem_self_4L m hmω) hmInm
    · have hcInc : c ∈ c := by simpa [hEq] using hmc
      exact (natural_not_mem_self_4L c hcω) hcInc
  have hcA : c ∈ A := hStep c hcω hAllSmallA
  exact hcNotA hcA

abbrev natural_le_iff_subset := cor_4M_le_iff_subset

/- [Enderton, Corollary 4Q, p.88] -/
theorem cor_4Q_no_descending_omega_sequence :
    ¬ ∃ (f : Set → Set), (∀ n, n ∈ ω → f n ∈ ω) ∧ (∀ n, n ∈ ω → f (n⁺) ∈ f n) := by
  intro h
  rcases h with ⟨f, hInω, hDesc⟩
  let Rset : Set := Comprehension (fun y => ∃ n, n ∈ ω ∧ y = f n) ω
  have hRspec : ∀ y, y ∈ Rset ↔ y ∈ ω ∧ ∃ n, n ∈ ω ∧ y = f n := by
    intro y
    simp [Rset, Comprehension.Spec]
  have hRne : Rset.Nonempty := by
    refine ⟨f Set.Empty, ?_⟩
    rw [hRspec]
    refine ⟨hInω Set.Empty thm_4B_ω_inductive.left, ?_⟩
    exact ⟨Set.Empty, thm_4B_ω_inductive.left, rfl⟩
  have hRsub : Rset ⊆ ω := by
    intro y hy
    exact (hRspec y).1 hy |>.left
  rcases omega_well_ordering Rset hRsub hRne with ⟨m, hmR, hmLeast⟩
  rcases (hRspec m).1 hmR with ⟨hmω, n, hnω, hmEq⟩
  have hnSuccω : n⁺ ∈ ω := thm_4B_ω_inductive.right n hnω
  have hmnSucc : f (n⁺) ∈ m := by simpa [hmEq] using hDesc n hnω
  have hfnSuccR : f (n⁺) ∈ Rset := by
    rw [hRspec]
    refine ⟨hInω (n⁺) hnSuccω, ?_⟩
    exact ⟨n⁺, hnSuccω, rfl⟩
  rcases hmLeast (f (n⁺)) hfnSuccR with hmInFnSucc | hmEqSucc
  · have hmTrans : IsTransitiveSet m := natural_transitive_set m ((ω.Spec).1 hmω)
    have hmInm : m ∈ m := hmTrans m (f (n⁺)) hmInFnSucc hmnSucc
    exact (natural_not_mem_self_4L m hmω) hmInm
  · have hmInm : m ∈ m := by simpa [hmEqSucc] using hmnSucc
    exact (natural_not_mem_self_4L m hmω) hmInm

abbrev no_descending_omega_sequence := cor_4Q_no_descending_omega_sequence

/- [Enderton, Theorem 4N (addition monotonicity component), pp.85-86] -/
theorem thm_4N_order_preserved_by_add
  (m n k : Set) :
  m ∈ ω → n ∈ ω → k ∈ ω → m ∈ n → (m + k) ∈ (n + k) := by
  intro hmω hnω hkω hmn
  have hAll : ∀ t, t ∈ ω → (m + t) ∈ (n + t) := by
    apply ω_induction (fun t => (m + t) ∈ (n + t))
    · have hm0 : m + Set.Empty = m := by simpa [zero_ω] using nat_add_zero m hmω
      have hn0 : n + Set.Empty = n := by simpa [zero_ω] using nat_add_zero n hnω
      simpa [hm0, hn0] using hmn
    · intro t htω hmtnt
      have hmAddω : m + t ∈ ω := nat_add_closed m t hmω htω
      have hnAddω : n + t ∈ ω := nat_add_closed n t hnω htω
      have hSuccMem : (m + t)⁺ ∈ (n + t)⁺ :=
        (natural_succ_mem_iff (m + t) (n + t) hmAddω hnAddω).1 hmtnt
      have hmSuccEq : m + t⁺ = (m + t)⁺ := nat_add_succ m t hmω htω
      have hnSuccEq : n + t⁺ = (n + t)⁺ := nat_add_succ n t hnω htω
      simpa [hmSuccEq, hnSuccEq] using hSuccMem
  exact hAll k hkω

abbrev nat_order_preserved_by_add := thm_4N_order_preserved_by_add

/- [Enderton, Theorem 4N (multiplication monotonicity, successor factor), pp.85-86] -/
theorem thm_4N_order_preserved_by_mul_succ_factor
  (m n p : Set) :
  m ∈ ω → n ∈ ω → p ∈ ω → m ∈ n → (m * p⁺) ∈ (n * p⁺) := by
  intro hmω hnω hpω hmn
  have hAll : ∀ t, t ∈ ω → (m * t⁺) ∈ (n * t⁺) := by
    apply ω_induction (fun t => (m * t⁺) ∈ (n * t⁺))
    · have h0ω : Set.Empty ∈ ω := thm_4B_ω_inductive.left
      have hmZero : m * Set.Empty = Set.Empty := by
        simpa [zero_ω] using (nat_mul_zero m hmω)
      have hm1 : m * Set.Empty⁺ = m := by
        calc
          m * Set.Empty⁺ = (m * Set.Empty) + m := nat_mul_succ m Set.Empty hmω h0ω
          _ = Set.Empty + m := by simp [hmZero]
          _ = m := nat_zero_add m hmω
      have hnZero : n * Set.Empty = Set.Empty := by
        simpa [zero_ω] using (nat_mul_zero n hnω)
      have hn1 : n * Set.Empty⁺ = n := by
        calc
          n * Set.Empty⁺ = (n * Set.Empty) + n := nat_mul_succ n Set.Empty hnω h0ω
          _ = Set.Empty + n := by simp [hnZero]
          _ = n := nat_zero_add n hnω
      simpa [hm1, hn1] using hmn
    · intro t htω hmtp
      have htSuccω : t⁺ ∈ ω := thm_4B_ω_inductive.right t htω
      have hmtω : m * t⁺ ∈ ω := nat_mul_closed m (t⁺) hmω htSuccω
      have hntω : n * t⁺ ∈ ω := nat_mul_closed n (t⁺) hnω htSuccω
      have h1 : (m * t⁺) + m ∈ (n * t⁺) + m :=
        nat_order_preserved_by_add (m * t⁺) (n * t⁺) m hmtω hntω hmω hmtp
      have h2raw : m + (n * t⁺) ∈ n + (n * t⁺) :=
        nat_order_preserved_by_add m n (n * t⁺) hmω hnω hntω hmn
      have h2 : (n * t⁺) + m ∈ (n * t⁺) + n := by
        simpa [nat_add_comm (n * t⁺) m hntω hmω, nat_add_comm (n * t⁺) n hntω hnω] using h2raw
      have hmsEq : m * (t⁺)⁺ = (m * t⁺) + m := nat_mul_succ m (t⁺) hmω htSuccω
      have hnsEq : n * (t⁺)⁺ = (n * t⁺) + n := nat_mul_succ n (t⁺) hnω htSuccω
      have hnsSuccω : n * ((t⁺)⁺) ∈ ω := nat_mul_closed n ((t⁺)⁺) hnω (thm_4B_ω_inductive.right (t⁺) htSuccω)
      have hab : m * (t⁺)⁺ ∈ (n * t⁺) + m := by simpa [hmsEq] using h1
      have hbc : (n * t⁺) + m ∈ n * (t⁺)⁺ := by simpa [hnsEq] using h2
      have hTrans : IsTransitiveSet (n * (t⁺)⁺) :=
        natural_transitive_set (n * (t⁺)⁺) ((ω.Spec).1 hnsSuccω)
      exact hTrans (m * (t⁺)⁺) ((n * t⁺) + m) hab hbc
  exact hAll p hpω

abbrev nat_order_preserved_by_mul_succ_factor := thm_4N_order_preserved_by_mul_succ_factor

/- [Enderton, Theorem 4N (multiplication monotonicity, nonzero factor), pp.85-86] -/
theorem thm_4N_order_preserved_by_mul_nonzero
  (m n k : Set) :
  m ∈ ω → n ∈ ω → k ∈ ω → k ≠ zero_ω → m ∈ n → (m * k) ∈ (n * k) := by
  intro hmω hnω hkω hkNe hmn
  have hkNeEmpty : k ≠ Set.Empty := by simpa [zero_ω] using hkNe
  have hkNat : Natural k := (ω.Spec).1 hkω
  rcases thm_4C_omega_exists_successor k hkNeEmpty hkNat with ⟨p, hpω, hkEq⟩
  have hsucc : (m * p⁺) ∈ (n * p⁺) := nat_order_preserved_by_mul_succ_factor m n p hmω hnω hpω hmn
  simpa [hkEq] using hsucc

/- [Enderton, Theorem 4N, pp.85-86] -/
theorem thm_4N_order_preservation :
    (∀ m n k, m ∈ ω → n ∈ ω → k ∈ ω → m ∈ n → (m + k) ∈ (n + k)) ∧
    (∀ m n k, m ∈ ω → n ∈ ω → k ∈ ω → k ≠ zero_ω → m ∈ n → (m * k) ∈ (n * k)) :=
  ⟨thm_4N_order_preserved_by_add, thm_4N_order_preserved_by_mul_nonzero⟩

abbrev nat_order_preserved_by_mul_nonzero := thm_4N_order_preserved_by_mul_nonzero

/- [Enderton, Corollary 4P (addition cancellation component), pp.86-87] -/
theorem cor_4P_add_right_cancel
  (a b k : Set) :
  a ∈ ω → b ∈ ω → k ∈ ω → a + k = b + k → a = b := by
  intro haω hbω hkω hEq
  rcases natural_compare a b haω hbω with hab | habEq | hba
  · exfalso
    have hmem : a + k ∈ b + k := nat_order_preserved_by_add a b k haω hbω hkω hab
    have hsumω : a + k ∈ ω := nat_add_closed a k haω hkω
    have hNot : (a + k) ∉ (a + k) := natural_not_mem_self_4L (a + k) hsumω
    exact hNot (by simpa [hEq] using hmem)
  · exact habEq
  · exfalso
    have hmem : b + k ∈ a + k := nat_order_preserved_by_add b a k hbω haω hkω hba
    have hsumω : b + k ∈ ω := nat_add_closed b k hbω hkω
    have hNot : (b + k) ∉ (b + k) := natural_not_mem_self_4L (b + k) hsumω
    exact hNot (by simpa [hEq] using hmem)

abbrev nat_add_right_cancel := cor_4P_add_right_cancel

/- [Enderton, Corollary 4P (multiplication cancellation component), pp.86-87] -/
theorem cor_4P_mul_right_cancel
  (a b k : Set) :
  a ∈ ω → b ∈ ω → k ∈ ω → k ≠ zero_ω → a * k = b * k → a = b := by
  intro haω hbω hkω hkNe hEq
  rcases natural_compare a b haω hbω with hab | habEq | hba
  · exfalso
    have hmem : a * k ∈ b * k :=
      nat_order_preserved_by_mul_nonzero a b k haω hbω hkω hkNe hab
    have hprodω : a * k ∈ ω := nat_mul_closed a k haω hkω
    have hNot : (a * k) ∉ (a * k) := natural_not_mem_self_4L (a * k) hprodω
    exact hNot (by simpa [hEq] using hmem)
  · exact habEq
  · exfalso
    have hmem : b * k ∈ a * k :=
      nat_order_preserved_by_mul_nonzero b a k hbω haω hkω hkNe hba
    have hprodω : b * k ∈ ω := nat_mul_closed b k hbω hkω
    have hNot : (b * k) ∉ (b * k) := natural_not_mem_self_4L (b * k) hprodω
    exact hNot (by simpa [hEq] using hmem)

/- [Enderton, Corollary 4P, pp.86-87] -/
theorem cor_4P_cancellation :
    (∀ a b k, a ∈ ω → b ∈ ω → k ∈ ω → a + k = b + k → a = b) ∧
    (∀ a b k, a ∈ ω → b ∈ ω → k ∈ ω → k ≠ zero_ω → a * k = b * k → a = b) :=
  ⟨cor_4P_add_right_cancel, cor_4P_mul_right_cancel⟩

abbrev nat_mul_right_cancel := cor_4P_mul_right_cancel

end Set
