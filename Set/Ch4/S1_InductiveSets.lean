import Set.Ch2

/-!
# Chapter 4, Section 1: Inductive Sets

Core natural-number construction in Enderton Ch4 §Inductive Sets.
-/

namespace Set

#check infinity

noncomputable def Successor (a : Set) : Set := a ∪ Singleton a
postfix:90 "⁺" => Successor

def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A

-- Derived Enderton-style infinity statement from the primitive declaration
-- in `Set/Axioms.lean`.
theorem infinity_inductive : ∃ (A : Set), Inductive A := by
  rcases (Set.infinity) with ⟨A, hEmpty, hSucc⟩
  rcases hEmpty with ⟨e, heEmpty, heA⟩
  refine ⟨A, ?_⟩
  constructor
  · have heq : e = Set.Empty := by
      apply extensionality
      intro x
      apply Iff.intro
      · intro hx
        exact (heEmpty x hx).elim
      · intro hx
        exact (Empty.Spec hx).elim
    simpa [heq] using heA
  · intro a ha
    rcases hSucc a ha with ⟨s, hsSpec, hsA⟩
    have hsEq : s = a⁺ := by
      apply extensionality
      intro x
      apply Iff.intro
      · intro hx
        have h : x ∈ a ∨ x = a := (hsSpec x).1 hx
        rw [Successor, Union.Spec, Singleton.Spec]
        exact h
      · intro hx
        rw [Successor, Union.Spec, Singleton.Spec] at hx
        exact (hsSpec x).2 hx
    simpa [hsEq] using hsA

-- A natural number is a set that belongs to every inductive set.
def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A

/- [Enderton, Theorem 4A, p.68] -/
theorem natural_numbers_exist : ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n := by
  obtain ⟨A, hA⟩ := infinity_inductive
  have hw : ∃ (w : Set), ∀ (x : Set), x ∈ w ↔ x ∈ A ∧ ∀ (A' : Set), A' ≠ A ∧ Inductive A' → x ∈ A' := by
    apply comprehension
  obtain ⟨w, hw⟩ := hw
  apply Exists.intro w
  intro n
  apply Iff.intro
  · intro hn
    intro a ha
    have h : n ∈ A ∧ ∀ (A' : Set), A' ≠ A ∧ Inductive A' → n ∈ A' := by aesop
    cases Classical.em (a = A) with
      | inl heq => aesop
      | inr hneq => aesop
  · aesop

noncomputable def ω := Classical.choose natural_numbers_exist

@[simp]
lemma ω.Spec {n : Set} : n ∈ ω ↔ Natural n := by
  have h := Classical.choose_spec natural_numbers_exist
  rw [ω]
  aesop

lemma natural_of_mem_omega (n : Set) : n ∈ ω → Natural n := by
  intro hnω
  exact (ω.Spec).1 hnω

lemma mem_omega_of_natural (n : Set) : Natural n → n ∈ ω := by
  intro hnNat
  exact (ω.Spec).2 hnNat

/- [Enderton, Theorem 4B, p.69] -/
theorem ω.inductive : Inductive ω := by
  rw [Inductive]
  apply And.intro
  · rw [ω.Spec, Natural]
    intro A hA
    rw [Inductive] at hA
    exact hA.left
  · intro n hn
    rw [ω.Spec, Natural]
    intro A hA
    obtain ⟨hA₁, hA₂⟩ := hA
    apply hA₂ n
    rw [ω.Spec] at hn
    rw [Natural] at hn
    apply hn
    rw [Inductive]
    exact And.intro hA₁ hA₂

theorem ω.subset_of_inductive : ∀ (A : Set), Inductive A → ω ⊆ A := by
  intro A hA
  intro n hn
  rw [ω.Spec] at hn
  rw [Natural] at hn
  apply hn
  exact hA


lemma ω_induction (P : Set → Prop)
    (hBase : P Set.Empty)
    (hStep : ∀ k, k ∈ ω → P k → P (k⁺)) :
    ∀ n, n ∈ ω → P n := by
  intro n hnω
  have hT : ∃ (T : Set), ∀ (k : Set), k ∈ T ↔ k ∈ ω ∧ P k := by
    apply comprehension
  obtain ⟨T, hTspec⟩ := hT
  have hTind : Inductive T := by
    rw [Inductive]
    refine ⟨?_, ?_⟩
    · exact (hTspec Set.Empty).2 ⟨ω.inductive.left, hBase⟩
    · intro k hk
      rcases (hTspec k).1 hk with ⟨hkω, hkP⟩
      exact (hTspec (k⁺)).2 ⟨ω.inductive.right k hkω, hStep k hkω hkP⟩
  have hωSubT : ω ⊆ T := ω.subset_of_inductive T hTind
  have hnT : n ∈ T := hωSubT n hnω
  exact (hTspec n).1 hnT |>.right

/- [Enderton, Theorem 4C, p.69] -/
theorem ω.exists_successor (n : Set) : n ≠ ∅ → Natural n → ∃ (m : Set), m ∈ ω ∧ n = m⁺ := by
  intro hneqe hnat
  have hT : ∃ (T : Set), ∀ (n : Set), n ∈ T ↔ n ∈ ω ∧ (n = Empty ∨ ∃ (p : Set), p ∈ ω ∧ n = p⁺) := by
    apply comprehension
  obtain ⟨T, hT⟩ := hT
  have hTn : n ∈ T ↔ n ∈ ω ∧ (n = Empty ∨ ∃ p, p ∈ ω ∧ n = p⁺) := by apply hT n
  have hTinductive : Inductive T := by
    rw [Inductive]
    apply And.intro
    · have he : ∅ ∈ ω := by
        rw [ω.Spec]
        intro A hA
        rw [Inductive] at hA
        exact hA.left
      aesop
    · intro k hk
      rw [hT] at hk
      obtain ⟨hk, h⟩ := hk
      cases h with
        | inl h =>
          rw [h]
          apply (hT (∅⁺)).mpr
          apply And.intro
          · rw [ω.Spec, Natural]
            intro A hA
            rw [Inductive] at hA
            obtain ⟨hA₁, hA₂⟩ := hA
            apply hA₂ ∅
            exact hA₁
          · aesop
        | inr h =>
          apply (hT (k⁺)).mpr
          apply And.intro
          · rw [ω.Spec, Natural]
            intro A hA
            obtain ⟨hA₁, hA₂⟩ := hA
            apply hA₂ k
            rw [ω.Spec, Natural] at hk
            apply hk A
            rw [Inductive]
            exact And.intro hA₁ hA₂
          · aesop
  have hnT : n ∈ T := by
    rw [Natural] at hnat
    apply hnat T hTinductive
  rw [hT] at hnT
  obtain ⟨_, h⟩ := hnT
  cases h with
    | inl h => contradiction
    | inr h => exact h

end Set
