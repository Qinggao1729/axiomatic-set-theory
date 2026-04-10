import Set.Ch4.S1_InductiveSets

/-!
# Chapter 4, Section 2: Peano's Postulates

Peano-system layer and transitive-set theorems from Enderton Ch4 §Peano's Postulates.
-/

namespace Set

def IsTransitiveSet (A : Set) : Prop :=
  ∀ (x a : Set), x ∈ a → a ∈ A → x ∈ A

def IsPeanoSystem (N : Set) (S : Set → Set) (e : Set) : Prop :=
  e ∈ N ∧
  (∀ n, n ∈ N → S n ∈ N) ∧
  (∀ n, n ∈ N → S n ≠ e) ∧
  (∀ m n, m ∈ N → n ∈ N → S m = S n → m = n) ∧
  (∀ A : Set, A ⊆ N → e ∈ A → (∀ x, x ∈ A → S x ∈ A) → A = N)

lemma successor_ne_empty (a : Set) : a⁺ ≠ ∅ := by
  intro h
  have ha : a ∈ a⁺ := by
    rw [Successor, Union.Spec]
    exact Or.inr (Singleton.Spec.2 rfl)
  have : a ∈ ∅ := by simp [h] at ha
  exact Empty.Spec this

/- [Enderton, Theorem 4E, p.72] -/
theorem bigunion_successor_of_transitive (a : Set) :
    IsTransitiveSet a → ⋃(a⁺) = a := by
  intro hTrans
  apply extensionality
  intro x
  apply Iff.intro
  · intro hx
    rw [BigUnion.Spec] at hx
    rcases hx with ⟨b, hb, hxb⟩
    rw [Successor, Union.Spec, Singleton.Spec] at hb
    cases hb with
    | inl hba =>
      exact hTrans x b hxb hba
    | inr hba =>
      rw [hba] at hxb
      exact hxb
  · intro hx
    rw [BigUnion.Spec]
    refine ⟨a, ?_, hx⟩
    rw [Successor, Union.Spec]
    exact Or.inr (Singleton.Spec.2 rfl)

/- [Enderton, Theorem 4F, p.72] -/
theorem natural_transitive_set (n : Set) : Natural n → IsTransitiveSet n := by
  intro hNat
  have hT : ∃ (T : Set), ∀ (x : Set), x ∈ T ↔ x ∈ ω ∧ IsTransitiveSet x := by
    apply comprehension
  obtain ⟨T, hTspec⟩ := hT
  have hTind : Inductive T := by
    rw [Inductive]
    refine ⟨?_, ?_⟩
    · have hEmptyTrans : IsTransitiveSet ∅ := by
        intro x a hxa ha
        exact (Empty.Spec ha).elim
      exact (hTspec ∅).2 ⟨ω.inductive.left, hEmptyTrans⟩
    · intro k hk
      rcases (hTspec k).1 hk with ⟨hkω, hkTrans⟩
      have hkSuccω : k⁺ ∈ ω := ω.inductive.right k hkω
      have hkSuccTrans : IsTransitiveSet (k⁺) := by
        intro x a hxa ha
        rw [Successor, Union.Spec, Singleton.Spec] at ha
        rw [Successor, Union.Spec]
        cases ha with
        | inl hak =>
          exact Or.inl (hkTrans x a hxa hak)
        | inr haeq =>
          rw [haeq] at hxa
          exact Or.inl hxa
      exact (hTspec (k⁺)).2 ⟨hkSuccω, hkSuccTrans⟩
  have hnT : n ∈ T := by
    rw [Natural] at hNat
    exact hNat T hTind
  exact (hTspec n).1 hnT |>.right

/- [Enderton, Theorem 4G, p.72] -/
theorem ω_transitive_set : IsTransitiveSet ω := by
  have hT : ∃ (T : Set), ∀ (x : Set), x ∈ T ↔ x ∈ ω ∧ x ⊆ ω := by
    apply comprehension
  obtain ⟨T, hTspec⟩ := hT
  have hTind : Inductive T := by
    rw [Inductive]
    refine ⟨?_, ?_⟩
    · have h0sub : ∅ ⊆ ω := by
        intro x hx
        exact (Empty.Spec hx).elim
      exact (hTspec ∅).2 ⟨ω.inductive.left, h0sub⟩
    · intro k hk
      rcases (hTspec k).1 hk with ⟨hkω, hkSub⟩
      have hkSuccω : k⁺ ∈ ω := ω.inductive.right k hkω
      have hkSuccSub : k⁺ ⊆ ω := by
        intro x hx
        rw [Successor, Union.Spec, Singleton.Spec] at hx
        cases hx with
        | inl hxk => exact hkSub x hxk
        | inr hxeq =>
          rw [hxeq]
          exact hkω
      exact (hTspec (k⁺)).2 ⟨hkSuccω, hkSuccSub⟩
  intro x a hxa haω
  have haNat : Natural a := (ω.Spec).1 haω
  have haT : a ∈ T := by
    rw [Natural] at haNat
    exact haNat T hTind
  have haSub : a ⊆ ω := (hTspec a).1 haT |>.right
  exact haSub x hxa

/- [Enderton, Theorem 4D, p.71] -/
theorem omega_peano_system : IsPeanoSystem ω (fun n => n⁺) ∅ := by
  refine ⟨ω.inductive.left, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact ω.inductive.right n hn
  · intro n hn
    exact successor_ne_empty n
  · intro m n hm hn hEq
    have hmTrans : IsTransitiveSet m := natural_transitive_set m ((ω.Spec).1 hm)
    have hnTrans : IsTransitiveSet n := natural_transitive_set n ((ω.Spec).1 hn)
    have hmU : ⋃(m⁺) = m := bigunion_successor_of_transitive m hmTrans
    have hnU : ⋃(n⁺) = n := bigunion_successor_of_transitive n hnTrans
    calc
      m = ⋃(m⁺) := hmU.symm
      _ = ⋃(n⁺) := by simp [hEq]
      _ = n := hnU
  · intro A hAω hA0 hASucc
    have hIndA : Inductive A := by
      rw [Inductive]
      exact ⟨hA0, hASucc⟩
    have hωA : ω ⊆ A := ω.subset_of_inductive A hIndA
    apply extensionality
    intro x
    apply Iff.intro
    · intro hx
      exact hAω x hx
    · intro hx
      exact hωA x hx

end Set
