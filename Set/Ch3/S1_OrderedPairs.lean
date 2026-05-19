import Set.Ch2.S2_ArbitraryUnionsIntersections
import Set.SimpAttrs

/-!
# Chapter 3, Section 1: Ordered Pairs

Ordered pair definitions and theorems (including 3A, 3B, 3C).
-/

namespace Set

/- Ordered Pair [Enderton, p. 36] -/
noncomputable def OrderedPair (x y : Set) : Set := Pair (Singleton x) (Pair x y)
@[simp]
lemma OrderedPair.Spec {x y w : Set} : w ∈ OrderedPair x y ↔ w = Singleton x ∨ w = Pair x y := by
  simp [OrderedPair, Pair.Spec, Singleton.Spec]
attribute [set_spec_simps] OrderedPair.Spec
notation:90 "⟨" x ", " y "⟩" => OrderedPair x y
notation:90 "⟪" x ", " y "⟫" => OrderedPair x y


lemma Singleton.eq_pair : ∀ {a b c : Set}, Singleton c = Pair a b → a = c ∧ b = c := by
    intro a b c h
    have ha : a ∈ Singleton c := by simp_all
    have ha : a = c := by simpa [] using ha
    have hb : b ∈ Singleton c := by simp_all
    have hb : b = c := by simpa [] using hb
    exact And.intro ha hb

@[simp]
lemma Singleton.eq_singleton_iff {a b : Set} : Singleton a = Singleton b ↔ a = b := by
  constructor
  · intro h
    have ha : a ∈ Singleton b := by
      rw [← h]
      simp []
    simpa only [Singleton.Spec] using ha
  · intro h
    rw [h]

lemma Pair.eq_pair_left_or {a b c d : Set} : Pair a b = Pair c d → a = c ∨ a = d := by
  intro h
  have ha : a ∈ Pair a b := by
    rw [Pair.Spec]
    exact Or.inl rfl
  have ha' : a ∈ Pair c d := by
    rw [← h]
    exact ha
  rw [Pair.Spec] at ha'
  exact ha'

lemma Pair.comm {a b : Set} : Pair a b = Pair b a := by
  apply extensionality
  intro x
  simp [Pair.Spec, or_comm]

lemma Pair.eq_pair_right_or {a b c d : Set} : Pair a b = Pair c d → b = c ∨ b = d := by
  intro h
  rw [Pair.comm] at h
  exact Pair.eq_pair_left_or h


/- [Enderton, Theorem 3A, p. 36] -/
theorem thm_3A_ordered_pair_uniqueness (u v x y : Set) :
  ⟪u, v⟫ = ⟪x, y⟫ ↔ u = x ∧ v = y := by
  constructor
  · intro h
    have h₁ : Singleton u = Singleton x ∨ Singleton u = Pair x y := by
      have huMem : Singleton u ∈ OrderedPair x y := by
        rw [← h]
        simp []
      simpa only [set_spec_simps] using huMem
    have h₂ : Pair u v = Singleton x ∨ Pair u v = Pair x y := by
      have huvMem : Pair u v ∈ OrderedPair x y := by
        rw [← h]
        simp []
      simpa only [set_spec_simps] using huvMem

    cases h₁ with
    | inl hux =>
      have hux : u = x := by
        simpa only [Singleton.eq_singleton_iff] using hux

      cases h₂ with
      | inl huvx =>  -- {u}={x} and {u,v}={x}
        have hvx : v = x := by
          have huvxSpec : u = x ∧ v = x := by
            exact (Singleton.eq_pair huvx.symm)
          exact huvxSpec.right
        simp_all
        have hxyMem' : Pair x y ∈ OrderedPair x x := by
          rw [h]
          simp []
        simp [Pair.Spec] at hxyMem'
        cases hxyMem' with
        | inl hxySingleton =>
          have ha := Singleton.eq_pair hxySingleton.symm
          simp only [ha]
        | inr hxyPair =>
          rw [huvx] at hxyPair
          have ha := Singleton.eq_pair hxyPair.symm
          simp only [ha]

      | inr huvxy =>  -- {u}={x} and {u,v}={x,y}
        have hvxy : v = x ∨ v = y := by
          exact Pair.eq_pair_right_or huvxy
        constructor
        · exact hux
        · cases hvxy with
          | inl hvx =>
            simp_all []
            exact (Singleton.eq_pair huvxy).2.symm
          | inr hvy =>
            exact hvy

    | inr huxy =>
      have huxy' : x = u ∧ y = u := Singleton.eq_pair huxy
      rcases huxy' with ⟨hxu, hyu⟩

      cases h₂ with
      | inl huvx =>  -- {u}={x,y} and {u,v}={x}
        have huvxSpec : u = x ∧ v = x := Singleton.eq_pair huvx.symm
        constructor
        · exact huvxSpec.left
        · simp only [huvxSpec.right, hxu, hyu]

      | inr huvxy =>  -- {u}={x,y} and {u,v}={x,y}
        simp_all []
        exact (Singleton.eq_pair huvxy.symm).2

  · intro h
    obtain ⟨hux, hvy⟩ := h
    rw [hux, hvy]

theorem OrderedPair.uniqueness (u v x y : Set) :
  ⟪u, v⟫ = ⟪x, y⟫ ↔ u = x ∧ v = y :=
  thm_3A_ordered_pair_uniqueness u v x y


/- [Enderton, Lemma 3B, p.37] -/
lemma lemma_3B_ordered_pair_in_power_power (x y C : Set) :
  x ∈ C → y ∈ C → OrderedPair x y ∈ Power (Power C) := by
  intro hx hy
  simp only [Power.Spec]
  simp only [SubsetOf, OrderedPair.Spec]
  simp only [Power.Spec, SubsetOf]
  simp []
  exact And.intro hx hy

lemma OrderedPair.in_power_power (x y C : Set) :
  x ∈ C → y ∈ C → OrderedPair x y ∈ Power (Power C) :=
  lemma_3B_ordered_pair_in_power_power x y C

lemma OrderedPair.product (A B : Set) :
  ∃ (C : Set), ∀ (w : Set), w ∈ C ↔ w ∈ 𝒫 𝒫 (A ∪ B) ∧ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫ := by
  obtain ⟨C, hC⟩ := comprehension (λ w ↦ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫) (𝒫 𝒫 (A ∪ B))
  exact ⟨C, hC⟩

noncomputable def Product (A B : Set) : Set := Classical.choose (OrderedPair.product A B)

@[simp]
lemma Product.Spec_full (A B : Set) : ∀ (w : Set), w ∈ Product A B ↔ w ∈ 𝒫 𝒫 (A ∪ B) ∧ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫ := by
  have h := Classical.choose_spec (OrderedPair.product A B)
  rw [Product]
  exact h

/- [Enderton, Corollary 3C, p.38] -/
@[simp]
lemma cor_3C_product_spec {A B w : Set} : w ∈ Product A B ↔ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫ := by
  constructor
  · intro hw
    have h :=(Product.Spec_full A B w).1 hw
    exact h.2
  · intro hw
    rcases hw with ⟨x, y, hxA, hyB, hEq⟩
    subst hEq
    have hxyPow : ⟪x, y⟫ ∈ 𝒫 𝒫 (A ∪ B) := by
      refine lemma_3B_ordered_pair_in_power_power x y (A ∪ B) ?_ ?_
      · simp [hxA]
      · simp [hyB]
    apply (Product.Spec_full A B (⟪x, y⟫)).2
    exact ⟨hxyPow, ⟨x, y, hxA, hyB, rfl⟩⟩
attribute [set_spec_simps] cor_3C_product_spec

@[simp]
lemma Product.Spec {A B w : Set} : w ∈ Product A B ↔ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫ :=
  cor_3C_product_spec
attribute [set_spec_simps] Product.Spec

infix:60 " ⨯ " => Product

@[simp]
lemma Product.Pair.Spec {A B x y : Set} : ⟪x, y⟫ ∈ Product A B ↔ x ∈ A ∧ y ∈ B := by
  constructor
  · intro hxy
    rcases (Product.Spec).1 hxy with ⟨u, v, huA, hvB, hEq⟩
    rcases (OrderedPair.uniqueness x y u v).1 hEq with ⟨hxu, hyv⟩
    subst hxu
    subst hyv
    exact ⟨huA, hvB⟩
  · intro hxy
    rcases hxy with ⟨hxA, hyB⟩
    exact (Product.Spec).2 ⟨x, y, hxA, hyB, rfl⟩
attribute [set_spec_simps] Product.Pair.Spec


end Set
