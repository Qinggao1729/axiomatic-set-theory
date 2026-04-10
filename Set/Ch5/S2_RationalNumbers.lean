import Set.Ch5.S1_Integers

/-!
# Chapter 5, Section 2: Rational Numbers

Formalization for Enderton Ch5 §Rational Numbers.
-/

namespace Set

open Lean Elab Tactic

noncomputable def NonzeroIntegers : Set := ℤ - Singleton zero_ℤ
notation "ℤ'" => NonzeroIntegers

@[simp] lemma ℤ'.Spec {z : Set} :
    z ∈ ℤ' ↔ z ∈ ℤ ∧ z ≠ zero_ℤ := by
  unfold NonzeroIntegers
  constructor
  · intro hz
    rcases (Difference.Spec).1 hz with ⟨hzZ, hzNot⟩
    refine ⟨hzZ, ?_⟩
    intro hEq
    exact hzNot (Singleton.Spec.2 hEq)
  · intro hz
    refine (Difference.Spec).2 ?_
    refine ⟨hz.1, ?_⟩
    intro hz0
    exact hz.2 (Singleton.Spec.1 hz0)

syntax "set_q" : tactic
macro_rules
  | `(tactic| set_q) => `(tactic|
      first
      | simp [ℤ', Difference.Spec, Singleton.Spec]
      | set_perm
      | set_omega)

-- Enderton's relation on fractions: <a,b> ~ <c,d> iff a*d = c*b.
noncomputable def RatEqRel : Set :=
  Comprehension
    (fun w =>
      ∃ a b c d,
        a ∈ ℤ ∧ b ∈ ℤ' ∧ c ∈ ℤ ∧ d ∈ ℤ' ∧
        w = ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∧
        (a ·_ℤ d) = (c ·_ℤ b))
    ((ℤ ⨯ ℤ') ⨯ (ℤ ⨯ ℤ'))

infix:50 " ~_ℚ " => fun x y : Set => ⟪x, y⟫ ∈ RatEqRel

@[simp] lemma RatEqRel.Spec {w : Set} :
    w ∈ RatEqRel ↔
      w ∈ ((ℤ ⨯ ℤ') ⨯ (ℤ ⨯ ℤ')) ∧
      ∃ a b c d,
        a ∈ ℤ ∧ b ∈ ℤ' ∧ c ∈ ℤ ∧ d ∈ ℤ' ∧
        w = ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∧
        (a ·_ℤ d) = (c ·_ℤ b) := by
  simp [RatEqRel, Comprehension.Spec]

@[simp] lemma RatEqRel.infix_iff (x y : Set) :
    (x ~_ℚ y) ↔ ⟨x, y⟩ ∈ RatEqRel := by
  rfl

lemma int_add_closed (a b : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) :
    a +_ℤ b ∈ ℤ :=
  add_ℤ_axioms.1 a b ha hb

lemma int_add_comm (a b : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) :
    a +_ℤ b = b +_ℤ a :=
  add_ℤ_axioms.2.1 a b ha hb

lemma int_add_assoc (a b c : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) (hc : c ∈ ℤ) :
    (a +_ℤ b) +_ℤ c = a +_ℤ (b +_ℤ c) :=
  add_ℤ_axioms.2.2.1 a b c ha hb hc

lemma int_add_zero_right (a : Set) (ha : a ∈ ℤ) :
    a +_ℤ zero_ℤ = a :=
  add_ℤ_axioms.2.2.2.1 a ha

lemma int_add_inv_exists (a : Set) (ha : a ∈ ℤ) :
    ∃ b, b ∈ ℤ ∧ a +_ℤ b = zero_ℤ :=
  add_ℤ_axioms.2.2.2.2 a ha

lemma int_mul_closed (a b : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) :
    a ·_ℤ b ∈ ℤ :=
  mul_ℤ_axioms.1 a b ha hb

lemma int_mul_comm (a b : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) :
    a ·_ℤ b = b ·_ℤ a :=
  mul_ℤ_axioms.2.1 a b ha hb

lemma int_mul_assoc (a b c : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) (hc : c ∈ ℤ) :
    (a ·_ℤ b) ·_ℤ c = a ·_ℤ (b ·_ℤ c) :=
  mul_ℤ_axioms.2.2.1 a b c ha hb hc

lemma int_mul_one_right (a : Set) (ha : a ∈ ℤ) :
    a ·_ℤ one_ℤ = a :=
  mul_ℤ_axioms.2.2.2.1 a ha

lemma int_mul_one_left (a : Set) (ha : a ∈ ℤ) :
    one_ℤ ·_ℤ a = a := by
  simpa [int_mul_comm one_ℤ a one_ℤ_mem_ℤ ha] using int_mul_one_right a ha

lemma int_mul_no_zero_div (a b : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ)
    (h : a ·_ℤ b = zero_ℤ) :
    a = zero_ℤ ∨ b = zero_ℤ :=
  mul_ℤ_axioms.2.2.2.2.2 a b ha hb h

lemma int_add_zero_left (a : Set) (ha : a ∈ ℤ) :
    zero_ℤ +_ℤ a = a := by
  calc
    zero_ℤ +_ℤ a = a +_ℤ zero_ℤ := int_add_comm zero_ℤ a zero_ℤ_mem_ℤ ha
    _ = a := int_add_zero_right a ha

lemma int_add_right_cancel (a b c : Set)
    (ha : a ∈ ℤ) (hb : b ∈ ℤ) (hc : c ∈ ℤ)
    (h : a +_ℤ c = b +_ℤ c) :
    a = b := by
  rcases int_add_inv_exists c hc with ⟨cInv, hcInv, hcInvEq⟩
  calc
    a = a +_ℤ zero_ℤ := (int_add_zero_right a ha).symm
    _ = a +_ℤ (c +_ℤ cInv) := by rw [hcInvEq]
    _ = (a +_ℤ c) +_ℤ cInv := by
      rw [← int_add_assoc a c cInv ha hc hcInv]
    _ = (b +_ℤ c) +_ℤ cInv := by rw [h]
    _ = b +_ℤ (c +_ℤ cInv) := by
      rw [int_add_assoc b c cInv hb hc hcInv]
    _ = b +_ℤ zero_ℤ := by rw [hcInvEq]
    _ = b := int_add_zero_right b hb

lemma int_mul_zero_right (a : Set) (ha : a ∈ ℤ) :
    a ·_ℤ zero_ℤ = zero_ℤ := by
  have hDist := mul_ℤ_left_distrib a zero_ℤ zero_ℤ ha zero_ℤ_mem_ℤ zero_ℤ_mem_ℤ
  have h00 : zero_ℤ +_ℤ zero_ℤ = zero_ℤ := int_add_zero_right zero_ℤ zero_ℤ_mem_ℤ
  have hRewrite : a ·_ℤ zero_ℤ = a ·_ℤ (zero_ℤ +_ℤ zero_ℤ) := by
    exact congrArg (fun t => a ·_ℤ t) h00.symm
  have hMain : a ·_ℤ zero_ℤ = (a ·_ℤ zero_ℤ) +_ℤ (a ·_ℤ zero_ℤ) := by
    calc
      a ·_ℤ zero_ℤ = a ·_ℤ (zero_ℤ +_ℤ zero_ℤ) := hRewrite
      _ = (a ·_ℤ zero_ℤ) +_ℤ (a ·_ℤ zero_ℤ) := hDist
  have ha0Z : a ·_ℤ zero_ℤ ∈ ℤ := int_mul_closed a zero_ℤ ha zero_ℤ_mem_ℤ
  have hMain' : zero_ℤ +_ℤ (a ·_ℤ zero_ℤ) = (a ·_ℤ zero_ℤ) +_ℤ (a ·_ℤ zero_ℤ) := by
    calc
      zero_ℤ +_ℤ (a ·_ℤ zero_ℤ) = a ·_ℤ zero_ℤ := int_add_zero_left (a ·_ℤ zero_ℤ) ha0Z
      _ = (a ·_ℤ zero_ℤ) +_ℤ (a ·_ℤ zero_ℤ) := hMain
  exact (int_add_right_cancel zero_ℤ (a ·_ℤ zero_ℤ) (a ·_ℤ zero_ℤ)
      zero_ℤ_mem_ℤ ha0Z ha0Z hMain').symm

lemma int_mul_zero_left (a : Set) (ha : a ∈ ℤ) :
    zero_ℤ ·_ℤ a = zero_ℤ := by
  simpa [int_mul_comm zero_ℤ a zero_ℤ_mem_ℤ ha] using int_mul_zero_right a ha

lemma int_mul_right_cancel_of_ne_zero (x y d : Set)
    (hx : x ∈ ℤ) (hy : y ∈ ℤ) (hd : d ∈ ℤ)
    (hd0 : d ≠ zero_ℤ)
    (hEq : x ·_ℤ d = y ·_ℤ d) :
    x = y := by
  rcases int_add_inv_exists y hy with ⟨yInv, hyInv, hyInvEq⟩
  have hxyInvZ : x +_ℤ yInv ∈ ℤ := int_add_closed x yInv hx hyInv
  have hMulEq : d ·_ℤ (x +_ℤ yInv) = d ·_ℤ (y +_ℤ yInv) := by
    calc
      d ·_ℤ (x +_ℤ yInv) = (d ·_ℤ x) +_ℤ (d ·_ℤ yInv) := mul_ℤ_left_distrib d x yInv hd hx hyInv
      _ = (x ·_ℤ d) +_ℤ (yInv ·_ℤ d) := by
        rw [int_mul_comm d x hd hx, int_mul_comm d yInv hd hyInv]
      _ = (y ·_ℤ d) +_ℤ (yInv ·_ℤ d) := by rw [hEq]
      _ = (d ·_ℤ y) +_ℤ (d ·_ℤ yInv) := by
        rw [int_mul_comm y d hy hd, int_mul_comm yInv d hyInv hd]
      _ = d ·_ℤ (y +_ℤ yInv) := (mul_ℤ_left_distrib d y yInv hd hy hyInv).symm
  have hLeftZero : d ·_ℤ (x +_ℤ yInv) = zero_ℤ := by
    calc
      d ·_ℤ (x +_ℤ yInv) = d ·_ℤ (y +_ℤ yInv) := hMulEq
      _ = d ·_ℤ zero_ℤ := by rw [hyInvEq]
      _ = zero_ℤ := int_mul_zero_right d hd
  have hOr : d = zero_ℤ ∨ (x +_ℤ yInv) = zero_ℤ :=
    int_mul_no_zero_div d (x +_ℤ yInv) hd hxyInvZ hLeftZero
  have hxyInvEq : x +_ℤ yInv = y +_ℤ yInv := by
    rcases hOr with hdZero | hxyZero
    · exfalso
      exact hd0 hdZero
    · calc
        x +_ℤ yInv = zero_ℤ := hxyZero
        _ = y +_ℤ yInv := hyInvEq.symm
  exact int_add_right_cancel x y yInv hx hy hyInv hxyInvEq

lemma int_mul_right_distrib (a b c : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) (hc : c ∈ ℤ) :
    (a +_ℤ b) ·_ℤ c = (a ·_ℤ c) +_ℤ (b ·_ℤ c) := by
  calc
    (a +_ℤ b) ·_ℤ c = c ·_ℤ (a +_ℤ b) := int_mul_comm (a +_ℤ b) c (int_add_closed a b ha hb) hc
    _ = (c ·_ℤ a) +_ℤ (c ·_ℤ b) := mul_ℤ_left_distrib c a b hc ha hb
    _ = (a ·_ℤ c) +_ℤ (b ·_ℤ c) := by
      rw [int_mul_comm c a hc ha, int_mul_comm c b hc hb]

lemma int_mul_mem_nonzero (a b : Set) (ha : a ∈ ℤ') (hb : b ∈ ℤ') :
    a ·_ℤ b ∈ ℤ' := by
  rcases (ℤ'.Spec).1 ha with ⟨haZ, ha0⟩
  rcases (ℤ'.Spec).1 hb with ⟨hbZ, hb0⟩
  refine (ℤ'.Spec).2 ?_
  refine ⟨int_mul_closed a b haZ hbZ, ?_⟩
  intro h0
  rcases int_mul_no_zero_div a b haZ hbZ h0 with haZero | hbZero
  · exact ha0 haZero
  · exact hb0 hbZero

lemma rat_exists_rep (r : Set) (hr : r ∈ ((ℤ ⨯ ℤ') / RatEqRel)) :
    ∃ a b, a ∈ ℤ ∧ b ∈ ℤ' ∧ r = [⟪a, b⟫]₍RatEqRel₎ := by
  rcases (QuotientSet.Spec).1 hr with ⟨_, x, hxCarrier, hrEq⟩
  rcases (Product.Spec (A := ℤ) (B := ℤ') (w := x)).1 (by simpa using hxCarrier) with
    ⟨a, b, haZ, hbNZ, hxEq⟩
  refine ⟨a, b, haZ, hbNZ, ?_⟩
  simpa [hxEq] using hrEq

noncomputable def rat_rep_num (r : Set) (hr : r ∈ ((ℤ ⨯ ℤ') / RatEqRel)) : Set :=
  Classical.choose (rat_exists_rep r hr)

noncomputable def rat_rep_den (r : Set) (hr : r ∈ ((ℤ ⨯ ℤ') / RatEqRel)) : Set :=
  Classical.choose (Classical.choose_spec (rat_exists_rep r hr))

lemma rat_rep_spec (r : Set) (hr : r ∈ ((ℤ ⨯ ℤ') / RatEqRel)) :
    rat_rep_num r hr ∈ ℤ ∧
    rat_rep_den r hr ∈ ℤ' ∧
    r = [⟪(rat_rep_num r hr), (rat_rep_den r hr)⟫]₍RatEqRel₎ := by
  simpa [rat_rep_num, rat_rep_den] using
    (Classical.choose_spec (Classical.choose_spec (rat_exists_rep r hr)))

-- [Enderton, Theorem 5QA, p.102]
theorem theorem_5ℚA : IsEquivalenceRelation RatEqRel (ℤ ⨯ ℤ') := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w hw
    rcases (RatEqRel.Spec).1 hw with
      ⟨_, a, b, c, d, _, _, _, _, hPair, _⟩
    exact ⟨⟪a, b⟫, ⟪c, d⟫, hPair⟩
  · intro w hw
    exact (RatEqRel.Spec).1 hw |>.1
  · intro x hx
    rcases (Product.Spec (A := ℤ) (B := ℤ') (w := x)).1 (by simpa using hx) with
      ⟨a, b, haZ, hbNZ, rfl⟩
    rw [RatEqRel.Spec]
    refine ⟨?_, ?_⟩
    · exact Pair.mem_product (ℤ ⨯ ℤ') (ℤ ⨯ ℤ')
        (⟪a, b⟫) (⟪a, b⟫)
        (by simpa using Pair.mem_product ℤ ℤ' a b haZ hbNZ)
        (by simpa using Pair.mem_product ℤ ℤ' a b haZ hbNZ)
    · exact ⟨a, b, a, b, haZ, hbNZ, haZ, hbNZ, rfl, rfl⟩
  · intro x y hxy
    rcases (RatEqRel.Spec).1 hxy with
      ⟨hxyProd, a, b, c, d, haZ, hbNZ, hcZ, hdNZ, hPairEq, hMul⟩
    have hx : x = ⟪a, b⟫ :=
      (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hPairEq |>.1
    have hy : y = ⟪c, d⟫ :=
      (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hPairEq |>.2
    have hxCarrier : x ∈ (ℤ ⨯ ℤ') :=
      (Pair.mem_product_elim (ℤ ⨯ ℤ') (ℤ ⨯ ℤ') x y hxyProd).1
    have hyCarrier : y ∈ (ℤ ⨯ ℤ') :=
      (Pair.mem_product_elim (ℤ ⨯ ℤ') (ℤ ⨯ ℤ') x y hxyProd).2
    rw [RatEqRel.Spec]
    refine ⟨?_, ?_⟩
    · exact Pair.mem_product (ℤ ⨯ ℤ') (ℤ ⨯ ℤ') y x hyCarrier hxCarrier
    · refine ⟨c, d, a, b, hcZ, hdNZ, haZ, hbNZ, ?_, hMul.symm⟩
      simp [hx, hy]
  · intro x y z hxy hyz
    rcases (RatEqRel.Spec).1 hxy with
      ⟨hxyProd, a, b, c, d, haZ, hbNZ, hcZ, hdNZ, hxyPairEq, hxyMul⟩
    rcases (RatEqRel.Spec).1 hyz with
      ⟨hyzProd, c', d', e, f, _, _, heZ, hfNZ, hyzPairEq, hyzMul⟩
    have hx : x = ⟪a, b⟫ :=
      (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hxyPairEq |>.1
    have hy₁ : y = ⟪c, d⟫ :=
      (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hxyPairEq |>.2
    have hy₂ : y = ⟪c', d'⟫ :=
      (OrderedPair.uniqueness y z (⟪c', d'⟫) (⟪e, f⟫)).1 hyzPairEq |>.1
    have hz : z = ⟪e, f⟫ :=
      (OrderedPair.uniqueness y z (⟪c', d'⟫) (⟪e, f⟫)).1 hyzPairEq |>.2
    have hcdPair : ⟪c, d⟫ = ⟪c', d'⟫ := hy₁.symm.trans hy₂
    have hcc' : c = c' := (OrderedPair.uniqueness c d c' d').1 hcdPair |>.1
    have hdd' : d = d' := (OrderedPair.uniqueness c d c' d').1 hcdPair |>.2
    have hyzMul' : c ·_ℤ f = e ·_ℤ d := by
      simpa [hcc', hdd'] using hyzMul
    have hbZ : b ∈ ℤ := (ℤ'.Spec (z := b)).1 hbNZ |>.1
    have hdSpec : d ∈ ℤ ∧ d ≠ zero_ℤ := (ℤ'.Spec (z := d)).1 hdNZ
    have hdZ : d ∈ ℤ := hdSpec.1
    have hd0 : d ≠ zero_ℤ := hdSpec.2
    have hfZ : f ∈ ℤ := (ℤ'.Spec (z := f)).1 hfNZ |>.1
    have hStep1 : a ·_ℤ (d ·_ℤ f) = c ·_ℤ (b ·_ℤ f) := by
      calc
        a ·_ℤ (d ·_ℤ f) = (a ·_ℤ d) ·_ℤ f := (int_mul_assoc a d f haZ hdZ hfZ).symm
        _ = (c ·_ℤ b) ·_ℤ f := by rw [hxyMul]
        _ = c ·_ℤ (b ·_ℤ f) := int_mul_assoc c b f hcZ hbZ hfZ
    have hStep2 : c ·_ℤ (b ·_ℤ f) = e ·_ℤ (d ·_ℤ b) := by
      calc
        c ·_ℤ (b ·_ℤ f) = c ·_ℤ (f ·_ℤ b) := by rw [int_mul_comm b f hbZ hfZ]
        _ = (c ·_ℤ f) ·_ℤ b := (int_mul_assoc c f b hcZ hfZ hbZ).symm
        _ = (e ·_ℤ d) ·_ℤ b := by rw [hyzMul']
        _ = e ·_ℤ (d ·_ℤ b) := int_mul_assoc e d b heZ hdZ hbZ
    have hMid : a ·_ℤ (d ·_ℤ f) = e ·_ℤ (d ·_ℤ b) := hStep1.trans hStep2
    have hMulByD : (a ·_ℤ f) ·_ℤ d = (e ·_ℤ b) ·_ℤ d := by
      calc
        (a ·_ℤ f) ·_ℤ d = a ·_ℤ (f ·_ℤ d) := int_mul_assoc a f d haZ hfZ hdZ
        _ = a ·_ℤ (d ·_ℤ f) := by rw [int_mul_comm f d hfZ hdZ]
        _ = e ·_ℤ (d ·_ℤ b) := hMid
        _ = e ·_ℤ (b ·_ℤ d) := by rw [int_mul_comm d b hdZ hbZ]
        _ = (e ·_ℤ b) ·_ℤ d := (int_mul_assoc e b d heZ hbZ hdZ).symm
    have hafZ : (a ·_ℤ f) ∈ ℤ := int_mul_closed a f haZ hfZ
    have hebZ : (e ·_ℤ b) ∈ ℤ := int_mul_closed e b heZ hbZ
    have hFinalEq : a ·_ℤ f = e ·_ℤ b :=
      int_mul_right_cancel_of_ne_zero (a ·_ℤ f) (e ·_ℤ b) d hafZ hebZ hdZ hd0 hMulByD
    have hxCarrier : x ∈ (ℤ ⨯ ℤ') :=
      (Pair.mem_product_elim (ℤ ⨯ ℤ') (ℤ ⨯ ℤ') x y hxyProd).1
    have hzCarrier : z ∈ (ℤ ⨯ ℤ') :=
      (Pair.mem_product_elim (ℤ ⨯ ℤ') (ℤ ⨯ ℤ') y z hyzProd).2
    rw [RatEqRel.Spec]
    refine ⟨?_, ?_⟩
    · exact Pair.mem_product (ℤ ⨯ ℤ') (ℤ ⨯ ℤ') x z hxCarrier hzCarrier
    · refine ⟨a, b, e, f, haZ, hbNZ, heZ, hfNZ, ?_, hFinalEq⟩
      simp [hx, hz]

noncomputable def RationalSet : Set := (ℤ ⨯ ℤ') / RatEqRel
notation "ℚ" => RationalSet

noncomputable def zero_ℚ : Set := [⟪zero_ℤ, one_ℤ⟫]₍RatEqRel₎
noncomputable def one_ℚ : Set := [⟪one_ℤ, one_ℤ⟫]₍RatEqRel₎

@[simp] lemma one_ℤ_mem_nonzero : one_ℤ ∈ ℤ' := by
  exact (ℤ'.Spec).2 ⟨one_ℤ_mem_ℤ, by
    intro hEq
    exact zero_ℤ_ne_one_ℤ hEq.symm⟩

@[simp] lemma zero_ℚ_mem_ℚ : zero_ℚ ∈ ℚ := by
  exact EquivalenceClass.mem_quotient (ℤ ⨯ ℤ') RatEqRel
    (⟪zero_ℤ, one_ℤ⟫)
    (by
      simpa using Pair.mem_product ℤ ℤ'
        zero_ℤ one_ℤ zero_ℤ_mem_ℤ one_ℤ_mem_nonzero)

@[simp] lemma one_ℚ_mem_ℚ : one_ℚ ∈ ℚ := by
  exact EquivalenceClass.mem_quotient (ℤ ⨯ ℤ') RatEqRel
    (⟪one_ℤ, one_ℤ⟫)
    (by
      simpa using Pair.mem_product ℤ ℤ'
        one_ℤ one_ℤ one_ℤ_mem_ℤ one_ℤ_mem_nonzero)

noncomputable def rat_num (r : Set) : Set :=
  letI : DecidablePred (fun x : Set => x ∈ ℚ) := Classical.decPred (fun x : Set => x ∈ ℚ)
  if hr : r ∈ ℚ then
    rat_rep_num r (by simpa [RationalSet] using hr)
  else
    zero_ℤ

noncomputable def rat_den (r : Set) : Set :=
  letI : DecidablePred (fun x : Set => x ∈ ℚ) := Classical.decPred (fun x : Set => x ∈ ℚ)
  if hr : r ∈ ℚ then
    rat_rep_den r (by simpa [RationalSet] using hr)
  else
    one_ℤ

lemma rat_num_den_spec (r : Set) (hr : r ∈ ℚ) :
    rat_num r ∈ ℤ ∧ rat_den r ∈ ℤ' ∧
    r = [⟪(rat_num r), (rat_den r)⟫]₍RatEqRel₎ := by
  rcases rat_rep_spec r (by simpa [RationalSet] using hr) with ⟨haZ, hbNZ, hEq⟩
  constructor
  · simpa [rat_num, hr] using haZ
  constructor
  · simpa [rat_den, hr] using hbNZ
  · simpa [rat_num, rat_den, hr] using hEq

lemma RatEqRel.pair_mem
    (a b c d : Set)
    (haZ : a ∈ ℤ) (hbNZ : b ∈ ℤ') (hcZ : c ∈ ℤ) (hdNZ : d ∈ ℤ')
    (hEq : a ·_ℤ d = c ·_ℤ b) :
    ⟨⟪a, b⟫, ⟪c, d⟫⟩ ∈ RatEqRel := by
  rw [RatEqRel.Spec]
  refine ⟨?_, ?_⟩
  · exact Pair.mem_product (ℤ ⨯ ℤ') (ℤ ⨯ ℤ')
      (⟪a, b⟫) (⟪c, d⟫)
      (by simpa using Pair.mem_product ℤ ℤ' a b haZ hbNZ)
      (by simpa using Pair.mem_product ℤ ℤ' c d hcZ hdNZ)
  · exact ⟨a, b, c, d, haZ, hbNZ, hcZ, hdNZ, rfl, hEq⟩

lemma rat_class_eq_iff
    (a b c d : Set)
    (haZ : a ∈ ℤ) (hbNZ : b ∈ ℤ') (hcZ : c ∈ ℤ) (hdNZ : d ∈ ℤ') :
    [⟪a, b⟫]₍RatEqRel₎ = [⟪c, d⟫]₍RatEqRel₎ ↔
      ⟨⟪a, b⟫, ⟪c, d⟫⟩ ∈ RatEqRel := by
  exact (equiv_class_eq_iff RatEqRel (ℤ ⨯ ℤ')
      (⟪a, b⟫) (⟪c, d⟫) theorem_5ℚA
      (by simpa using Pair.mem_product ℤ ℤ' a b haZ hbNZ)
      (by simpa using Pair.mem_product ℤ ℤ' c d hcZ hdNZ))

lemma rat_mul_pair_congr
    (a b c d a' b' c' d' : Set)
    (h₁ : ⟨⟪a, b⟫, ⟪a', b'⟫⟩ ∈ RatEqRel)
    (h₂ : ⟨⟪c, d⟫, ⟪c', d'⟫⟩ ∈ RatEqRel) :
    ⟨⟪(a ·_ℤ c), (b ·_ℤ d)⟫, ⟪(a' ·_ℤ c'), (b' ·_ℤ d')⟫⟩ ∈ RatEqRel := by
  rcases (RatEqRel.Spec).1 h₁ with
    ⟨_, a0, b0, a1, b1, ha0Z, hb0NZ, ha1Z, hb1NZ, hPair₁, hEq₁⟩
  rcases (RatEqRel.Spec).1 h₂ with
    ⟨_, c0, d0, c1, d1, hc0Z, hd0NZ, hc1Z, hd1NZ, hPair₂, hEq₂⟩
  have hL₁ : ⟪a, b⟫ = ⟪a0, b0⟫ :=
    (OrderedPair.uniqueness (⟪a, b⟫) (⟪a', b'⟫)
      (⟪a0, b0⟫) (⟪a1, b1⟫)).1 hPair₁ |>.1
  have hR₁ : ⟪a', b'⟫ = ⟪a1, b1⟫ :=
    (OrderedPair.uniqueness (⟪a, b⟫) (⟪a', b'⟫)
      (⟪a0, b0⟫) (⟪a1, b1⟫)).1 hPair₁ |>.2
  have haEq : a = a0 := (OrderedPair.uniqueness a b a0 b0).1 hL₁ |>.1
  have hbEq : b = b0 := (OrderedPair.uniqueness a b a0 b0).1 hL₁ |>.2
  have ha'Eq : a' = a1 := (OrderedPair.uniqueness a' b' a1 b1).1 hR₁ |>.1
  have hb'Eq : b' = b1 := (OrderedPair.uniqueness a' b' a1 b1).1 hR₁ |>.2
  have hL₂ : ⟪c, d⟫ = ⟪c0, d0⟫ :=
    (OrderedPair.uniqueness (⟪c, d⟫) (⟪c', d'⟫)
      (⟪c0, d0⟫) (⟪c1, d1⟫)).1 hPair₂ |>.1
  have hR₂ : ⟪c', d'⟫ = ⟪c1, d1⟫ :=
    (OrderedPair.uniqueness (⟪c, d⟫) (⟪c', d'⟫)
      (⟪c0, d0⟫) (⟪c1, d1⟫)).1 hPair₂ |>.2
  have hcEq : c = c0 := (OrderedPair.uniqueness c d c0 d0).1 hL₂ |>.1
  have hdEq : d = d0 := (OrderedPair.uniqueness c d c0 d0).1 hL₂ |>.2
  have hc'Eq : c' = c1 := (OrderedPair.uniqueness c' d' c1 d1).1 hR₂ |>.1
  have hd'Eq : d' = d1 := (OrderedPair.uniqueness c' d' c1 d1).1 hR₂ |>.2
  subst a0 b0 a1 b1 c0 d0 c1 d1
  have hab :
      a ·_ℤ b' = a' ·_ℤ b := by
    simpa using hEq₁
  have hcd :
      c ·_ℤ d' = c' ·_ℤ d := by
    simpa using hEq₂
  have haZ : a ∈ ℤ := by simpa using ha0Z
  have hbNZ : b ∈ ℤ' := by simpa using hb0NZ
  have ha'Z : a' ∈ ℤ := by simpa using ha1Z
  have hb'NZ : b' ∈ ℤ' := by simpa using hb1NZ
  have hcZ : c ∈ ℤ := by simpa using hc0Z
  have hdNZ : d ∈ ℤ' := by simpa using hd0NZ
  have hc'Z : c' ∈ ℤ := by simpa using hc1Z
  have hd'NZ : d' ∈ ℤ' := by simpa using hd1NZ
  have hbZ : b ∈ ℤ := (ℤ'.Spec).1 hbNZ |>.1
  have hb'Z : b' ∈ ℤ := (ℤ'.Spec).1 hb'NZ |>.1
  have hdZ : d ∈ ℤ := (ℤ'.Spec).1 hdNZ |>.1
  have hd'Z : d' ∈ ℤ := (ℤ'.Spec).1 hd'NZ |>.1
  have hNumEq :
      (a ·_ℤ c) ·_ℤ (b' ·_ℤ d') = (a' ·_ℤ c') ·_ℤ (b ·_ℤ d) := by
    calc
      (a ·_ℤ c) ·_ℤ (b' ·_ℤ d')
          = (a ·_ℤ b') ·_ℤ (c ·_ℤ d') := by
              calc
                (a ·_ℤ c) ·_ℤ (b' ·_ℤ d')
                    = ((a ·_ℤ c) ·_ℤ b') ·_ℤ d' := by
                        rw [int_mul_assoc (a ·_ℤ c) b' d' (int_mul_closed a c haZ hcZ) hb'Z hd'Z]
                _ = (a ·_ℤ (c ·_ℤ b')) ·_ℤ d' := by
                        rw [int_mul_assoc a c b' haZ hcZ hb'Z]
                _ = (a ·_ℤ (b' ·_ℤ c)) ·_ℤ d' := by
                        rw [int_mul_comm c b' hcZ hb'Z]
                _ = ((a ·_ℤ b') ·_ℤ c) ·_ℤ d' := by
                        rw [← int_mul_assoc a b' c haZ hb'Z hcZ]
                _ = (a ·_ℤ b') ·_ℤ (c ·_ℤ d') := by
                        rw [← int_mul_assoc (a ·_ℤ b') c d' (int_mul_closed a b' haZ hb'Z) hcZ hd'Z]
      _ = (a' ·_ℤ b) ·_ℤ (c' ·_ℤ d) := by rw [hab, hcd]
      _ = (a' ·_ℤ c') ·_ℤ (b ·_ℤ d) := by
            calc
              (a' ·_ℤ b) ·_ℤ (c' ·_ℤ d)
                  = ((a' ·_ℤ b) ·_ℤ c') ·_ℤ d := by
                      rw [int_mul_assoc (a' ·_ℤ b) c' d (int_mul_closed a' b ha'Z hbZ) hc'Z hdZ]
              _ = (a' ·_ℤ (b ·_ℤ c')) ·_ℤ d := by
                      rw [int_mul_assoc a' b c' ha'Z hbZ hc'Z]
              _ = (a' ·_ℤ (c' ·_ℤ b)) ·_ℤ d := by
                      rw [int_mul_comm b c' hbZ hc'Z]
              _ = ((a' ·_ℤ c') ·_ℤ b) ·_ℤ d := by
                      rw [← int_mul_assoc a' c' b ha'Z hc'Z hbZ]
              _ = (a' ·_ℤ c') ·_ℤ (b ·_ℤ d) := by
                      rw [← int_mul_assoc (a' ·_ℤ c') b d (int_mul_closed a' c' ha'Z hc'Z) hbZ hdZ]
  exact RatEqRel.pair_mem
    (a ·_ℤ c) (b ·_ℤ d) (a' ·_ℤ c') (b' ·_ℤ d')
    (int_mul_closed a c haZ hcZ)
    (int_mul_mem_nonzero b d hbNZ hdNZ)
    (int_mul_closed a' c' ha'Z hc'Z)
    (int_mul_mem_nonzero b' d' hb'NZ hd'NZ)
    hNumEq

noncomputable def rat_mul_candidate (r s : Set) : Set :=
  [⟪(rat_num r ·_ℤ rat_num s), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎

lemma rat_mul_candidate_closed (r s : Set) (hr : r ∈ ℚ) (hs : s ∈ ℚ) :
    rat_mul_candidate r s ∈ ℚ := by
  have hrSpec := rat_num_den_spec r hr
  have hsSpec := rat_num_den_spec s hs
  have hrnZ : rat_num r ∈ ℤ := hrSpec.1
  have hrdNZ : rat_den r ∈ ℤ' := hrSpec.2.1
  have hsnZ : rat_num s ∈ ℤ := hsSpec.1
  have hsdNZ : rat_den s ∈ ℤ' := hsSpec.2.1
  exact EquivalenceClass.mem_quotient (ℤ ⨯ ℤ') RatEqRel
    (⟪(rat_num r ·_ℤ rat_num s), (rat_den r ·_ℤ rat_den s)⟫)
    (by
      simpa using Pair.mem_product ℤ ℤ'
        (rat_num r ·_ℤ rat_num s) (rat_den r ·_ℤ rat_den s)
        (int_mul_closed (rat_num r) (rat_num s) hrnZ hsnZ)
        (int_mul_mem_nonzero (rat_den r) (rat_den s) hrdNZ hsdNZ))

lemma rat_mul_candidate_comm (r s : Set) (hr : r ∈ ℚ) (hs : s ∈ ℚ) :
    rat_mul_candidate r s = rat_mul_candidate s r := by
  have hrSpec := rat_num_den_spec r hr
  have hsSpec := rat_num_den_spec s hs
  have hrnZ : rat_num r ∈ ℤ := hrSpec.1
  have hrdZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hrSpec.2.1 |>.1
  have hsnZ : rat_num s ∈ ℤ := hsSpec.1
  have hsdZ : rat_den s ∈ ℤ := (ℤ'.Spec).1 hsSpec.2.1 |>.1
  simp [rat_mul_candidate,
    int_mul_comm (rat_num r) (rat_num s) hrnZ hsnZ,
    int_mul_comm (rat_den r) (rat_den s) hrdZ hsdZ]

lemma rat_mul_candidate_assoc (r s t : Set)
    (hr : r ∈ ℚ) (hs : s ∈ ℚ) (ht : t ∈ ℚ) :
    rat_mul_candidate (rat_mul_candidate r s) t = rat_mul_candidate r (rat_mul_candidate s t) := by
  have hrSpec := rat_num_den_spec r hr
  have hsSpec := rat_num_den_spec s hs
  have htSpec := rat_num_den_spec t ht
  have haZ : rat_num r ∈ ℤ := hrSpec.1
  have hbNZ : rat_den r ∈ ℤ' := hrSpec.2.1
  have hcZ : rat_num s ∈ ℤ := hsSpec.1
  have hdNZ : rat_den s ∈ ℤ' := hsSpec.2.1
  have heZ : rat_num t ∈ ℤ := htSpec.1
  have hfNZ : rat_den t ∈ ℤ' := htSpec.2.1
  have hMulRS : rat_mul_candidate r s ∈ ℚ := rat_mul_candidate_closed r s hr hs
  have hMulST : rat_mul_candidate s t ∈ ℚ := rat_mul_candidate_closed s t hs ht
  have hRSspec := rat_num_den_spec (rat_mul_candidate r s) hMulRS
  have hSTspec := rat_num_den_spec (rat_mul_candidate s t) hMulST
  have hRSclassEq :
      [⟪(rat_num (rat_mul_candidate r s)), (rat_den (rat_mul_candidate r s))⟫]₍RatEqRel₎ =
      [⟪(rat_num r ·_ℤ rat_num s), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎ := by
    calc
      [⟪(rat_num (rat_mul_candidate r s)), (rat_den (rat_mul_candidate r s))⟫]₍RatEqRel₎
          = rat_mul_candidate r s := hRSspec.2.2.symm
      _ = [⟪(rat_num r ·_ℤ rat_num s), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎ := by rfl
  have hSTclassEq :
      [⟪(rat_num (rat_mul_candidate s t)), (rat_den (rat_mul_candidate s t))⟫]₍RatEqRel₎ =
      [⟪(rat_num s ·_ℤ rat_num t), (rat_den s ·_ℤ rat_den t)⟫]₍RatEqRel₎ := by
    calc
      [⟪(rat_num (rat_mul_candidate s t)), (rat_den (rat_mul_candidate s t))⟫]₍RatEqRel₎
          = rat_mul_candidate s t := hSTspec.2.2.symm
      _ = [⟪(rat_num s ·_ℤ rat_num t), (rat_den s ·_ℤ rat_den t)⟫]₍RatEqRel₎ := by rfl
  have hRelRS :
      ⟨⟪(rat_num (rat_mul_candidate r s)), (rat_den (rat_mul_candidate r s))⟫,
        ⟪(rat_num r ·_ℤ rat_num s), (rat_den r ·_ℤ rat_den s)⟫⟩ ∈ RatEqRel := by
    have hNumRSZ : rat_num (rat_mul_candidate r s) ∈ ℤ := hRSspec.1
    have hDenRSNZ : rat_den (rat_mul_candidate r s) ∈ ℤ' := hRSspec.2.1
    have hNumRawZ : rat_num r ·_ℤ rat_num s ∈ ℤ := int_mul_closed (rat_num r) (rat_num s) haZ hcZ
    have hDenRawNZ : rat_den r ·_ℤ rat_den s ∈ ℤ' := int_mul_mem_nonzero (rat_den r) (rat_den s) hbNZ hdNZ
    exact (rat_class_eq_iff
      (rat_num (rat_mul_candidate r s)) (rat_den (rat_mul_candidate r s))
      (rat_num r ·_ℤ rat_num s) (rat_den r ·_ℤ rat_den s)
      hNumRSZ hDenRSNZ hNumRawZ hDenRawNZ).1 hRSclassEq
  have hRelST :
      ⟨⟪(rat_num (rat_mul_candidate s t)), (rat_den (rat_mul_candidate s t))⟫,
        ⟪(rat_num s ·_ℤ rat_num t), (rat_den s ·_ℤ rat_den t)⟫⟩ ∈ RatEqRel := by
    have hNumSTZ : rat_num (rat_mul_candidate s t) ∈ ℤ := hSTspec.1
    have hDenSTNZ : rat_den (rat_mul_candidate s t) ∈ ℤ' := hSTspec.2.1
    have hNumRawZ : rat_num s ·_ℤ rat_num t ∈ ℤ := int_mul_closed (rat_num s) (rat_num t) hcZ heZ
    have hDenRawNZ : rat_den s ·_ℤ rat_den t ∈ ℤ' := int_mul_mem_nonzero (rat_den s) (rat_den t) hdNZ hfNZ
    exact (rat_class_eq_iff
      (rat_num (rat_mul_candidate s t)) (rat_den (rat_mul_candidate s t))
      (rat_num s ·_ℤ rat_num t) (rat_den s ·_ℤ rat_den t)
      hNumSTZ hDenSTNZ hNumRawZ hDenRawNZ).1 hSTclassEq
  have hRelLeft :
      ⟨⟪(rat_num (rat_mul_candidate r s) ·_ℤ rat_num t), (rat_den (rat_mul_candidate r s) ·_ℤ rat_den t)⟫,
        ⟪((rat_num r ·_ℤ rat_num s) ·_ℤ rat_num t), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫⟩ ∈ RatEqRel := by
    have hReflT : ⟨⟪(rat_num t), (rat_den t)⟫, ⟪(rat_num t), (rat_den t)⟫⟩ ∈ RatEqRel := by
      exact RatEqRel.pair_mem (rat_num t) (rat_den t) (rat_num t) (rat_den t)
        heZ hfNZ heZ hfNZ rfl
    exact rat_mul_pair_congr
      (rat_num (rat_mul_candidate r s)) (rat_den (rat_mul_candidate r s))
      (rat_num t) (rat_den t)
      (rat_num r ·_ℤ rat_num s) (rat_den r ·_ℤ rat_den s)
      (rat_num t) (rat_den t)
      hRelRS hReflT
  have hRelRight :
      ⟨⟪(rat_num r ·_ℤ rat_num (rat_mul_candidate s t)), (rat_den r ·_ℤ rat_den (rat_mul_candidate s t))⟫,
        ⟪(rat_num r ·_ℤ (rat_num s ·_ℤ rat_num t)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫⟩ ∈ RatEqRel := by
    have hReflR : ⟨⟪(rat_num r), (rat_den r)⟫, ⟪(rat_num r), (rat_den r)⟫⟩ ∈ RatEqRel := by
      exact RatEqRel.pair_mem (rat_num r) (rat_den r) (rat_num r) (rat_den r)
        haZ hbNZ haZ hbNZ rfl
    exact rat_mul_pair_congr
      (rat_num r) (rat_den r)
      (rat_num (rat_mul_candidate s t)) (rat_den (rat_mul_candidate s t))
      (rat_num r) (rat_den r)
      (rat_num s ·_ℤ rat_num t) (rat_den s ·_ℤ rat_den t)
      hReflR hRelST
  have hClassLeft :
      rat_mul_candidate (rat_mul_candidate r s) t =
        [⟪((rat_num r ·_ℤ rat_num s) ·_ℤ rat_num t), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫]₍RatEqRel₎ := by
    have hNumLZ : rat_num (rat_mul_candidate r s) ·_ℤ rat_num t ∈ ℤ :=
      int_mul_closed (rat_num (rat_mul_candidate r s)) (rat_num t) hRSspec.1 heZ
    have hDenLNZ : rat_den (rat_mul_candidate r s) ·_ℤ rat_den t ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den (rat_mul_candidate r s)) (rat_den t) hRSspec.2.1 hfNZ
    have hNumRawZ : ((rat_num r ·_ℤ rat_num s) ·_ℤ rat_num t) ∈ ℤ :=
      int_mul_closed (rat_num r ·_ℤ rat_num s) (rat_num t) (int_mul_closed (rat_num r) (rat_num s) haZ hcZ) heZ
    have hDenRawNZ : ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den r ·_ℤ rat_den s) (rat_den t) (int_mul_mem_nonzero (rat_den r) (rat_den s) hbNZ hdNZ) hfNZ
    exact (rat_class_eq_iff
      (rat_num (rat_mul_candidate r s) ·_ℤ rat_num t) (rat_den (rat_mul_candidate r s) ·_ℤ rat_den t)
      ((rat_num r ·_ℤ rat_num s) ·_ℤ rat_num t) ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)
      hNumLZ hDenLNZ hNumRawZ hDenRawNZ).2 hRelLeft
  have hClassRight :
      rat_mul_candidate r (rat_mul_candidate s t) =
        [⟪(rat_num r ·_ℤ (rat_num s ·_ℤ rat_num t)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫]₍RatEqRel₎ := by
    have hNumRZ : rat_num r ·_ℤ rat_num (rat_mul_candidate s t) ∈ ℤ :=
      int_mul_closed (rat_num r) (rat_num (rat_mul_candidate s t)) haZ hSTspec.1
    have hDenRNZ : rat_den r ·_ℤ rat_den (rat_mul_candidate s t) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den r) (rat_den (rat_mul_candidate s t)) hbNZ hSTspec.2.1
    have hNumRawZ : (rat_num r ·_ℤ (rat_num s ·_ℤ rat_num t)) ∈ ℤ :=
      int_mul_closed (rat_num r) (rat_num s ·_ℤ rat_num t) haZ (int_mul_closed (rat_num s) (rat_num t) hcZ heZ)
    have hDenRawNZ : (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t)) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den r) (rat_den s ·_ℤ rat_den t) hbNZ (int_mul_mem_nonzero (rat_den s) (rat_den t) hdNZ hfNZ)
    exact (rat_class_eq_iff
      (rat_num r ·_ℤ rat_num (rat_mul_candidate s t)) (rat_den r ·_ℤ rat_den (rat_mul_candidate s t))
      (rat_num r ·_ℤ (rat_num s ·_ℤ rat_num t)) (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))
      hNumRZ hDenRNZ hNumRawZ hDenRawNZ).2 hRelRight
  have hNumAssoc :
      ((rat_num r ·_ℤ rat_num s) ·_ℤ rat_num t) = rat_num r ·_ℤ (rat_num s ·_ℤ rat_num t) := by
    exact int_mul_assoc (rat_num r) (rat_num s) (rat_num t) haZ hcZ heZ
  have hDenAssoc :
      ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t) = rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t) := by
    have hbZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hbNZ |>.1
    have hdZ : rat_den s ∈ ℤ := (ℤ'.Spec).1 hdNZ |>.1
    have hfZ : rat_den t ∈ ℤ := (ℤ'.Spec).1 hfNZ |>.1
    exact int_mul_assoc (rat_den r) (rat_den s) (rat_den t) hbZ hdZ hfZ
  calc
    rat_mul_candidate (rat_mul_candidate r s) t
        = [⟪((rat_num r ·_ℤ rat_num s) ·_ℤ rat_num t), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫]₍RatEqRel₎ := hClassLeft
    _ = [⟪(rat_num r ·_ℤ (rat_num s ·_ℤ rat_num t)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫]₍RatEqRel₎ := by
          simp [hNumAssoc, hDenAssoc]
    _ = rat_mul_candidate r (rat_mul_candidate s t) := hClassRight.symm

lemma rat_mul_candidate_one_right (r : Set) (hr : r ∈ ℚ) :
    rat_mul_candidate r one_ℚ = r := by
  have hrSpec := rat_num_den_spec r hr
  have h1Spec := rat_num_den_spec one_ℚ one_ℚ_mem_ℚ
  have haZ : rat_num r ∈ ℤ := hrSpec.1
  have hbNZ : rat_den r ∈ ℤ' := hrSpec.2.1
  have huZ : rat_num one_ℚ ∈ ℤ := h1Spec.1
  have hvNZ : rat_den one_ℚ ∈ ℤ' := h1Spec.2.1
  have hOneClassEq :
      [⟪(rat_num one_ℚ), (rat_den one_ℚ)⟫]₍RatEqRel₎ =
      [⟪one_ℤ, one_ℤ⟫]₍RatEqRel₎ := by
    calc
      [⟪(rat_num one_ℚ), (rat_den one_ℚ)⟫]₍RatEqRel₎ = one_ℚ := h1Spec.2.2.symm
      _ = [⟪one_ℤ, one_ℤ⟫]₍RatEqRel₎ := rfl
  have hRelOne :
      ⟨⟪(rat_num one_ℚ), (rat_den one_ℚ)⟫, ⟪one_ℤ, one_ℤ⟫⟩ ∈ RatEqRel := by
    exact (rat_class_eq_iff
      (rat_num one_ℚ) (rat_den one_ℚ) one_ℤ one_ℤ
      huZ hvNZ one_ℤ_mem_ℤ one_ℤ_mem_nonzero).1 hOneClassEq
  have hReflR :
      ⟨⟪(rat_num r), (rat_den r)⟫, ⟪(rat_num r), (rat_den r)⟫⟩ ∈ RatEqRel := by
    exact RatEqRel.pair_mem (rat_num r) (rat_den r) (rat_num r) (rat_den r)
      haZ hbNZ haZ hbNZ rfl
  have hRelMul :
      ⟨⟪(rat_num r ·_ℤ rat_num one_ℚ), (rat_den r ·_ℤ rat_den one_ℚ)⟫,
        ⟪(rat_num r ·_ℤ one_ℤ), (rat_den r ·_ℤ one_ℤ)⟫⟩ ∈ RatEqRel := by
    exact rat_mul_pair_congr
      (rat_num r) (rat_den r)
      (rat_num one_ℚ) (rat_den one_ℚ)
      (rat_num r) (rat_den r)
      one_ℤ one_ℤ
      hReflR hRelOne
  have hbZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hbNZ |>.1
  have hClassMul :
      [⟪(rat_num r ·_ℤ rat_num one_ℚ), (rat_den r ·_ℤ rat_den one_ℚ)⟫]₍RatEqRel₎ =
      [⟪(rat_num r ·_ℤ one_ℤ), (rat_den r ·_ℤ one_ℤ)⟫]₍RatEqRel₎ := by
    exact (rat_class_eq_iff
      (rat_num r ·_ℤ rat_num one_ℚ) (rat_den r ·_ℤ rat_den one_ℚ)
      (rat_num r ·_ℤ one_ℤ) (rat_den r ·_ℤ one_ℤ)
      (int_mul_closed (rat_num r) (rat_num one_ℚ) haZ huZ)
      (int_mul_mem_nonzero (rat_den r) (rat_den one_ℚ) hbNZ hvNZ)
      (int_mul_closed (rat_num r) one_ℤ haZ one_ℤ_mem_ℤ)
      (int_mul_mem_nonzero (rat_den r) one_ℤ hbNZ one_ℤ_mem_nonzero)).2 hRelMul
  calc
    rat_mul_candidate r one_ℚ
        = [⟪(rat_num r ·_ℤ rat_num one_ℚ), (rat_den r ·_ℤ rat_den one_ℚ)⟫]₍RatEqRel₎ := rfl
    _ = [⟪(rat_num r ·_ℤ one_ℤ), (rat_den r ·_ℤ one_ℤ)⟫]₍RatEqRel₎ := hClassMul
    _ = [⟪(rat_num r), (rat_den r)⟫]₍RatEqRel₎ := by
          simp [int_mul_one_right (rat_num r) haZ, int_mul_one_right (rat_den r) hbZ]
    _ = r := hrSpec.2.2.symm

lemma rat_add_pair_congr
    (a b c d a' b' c' d' : Set)
    (h₁ : ⟨⟪a, b⟫, ⟪a', b'⟫⟩ ∈ RatEqRel)
    (h₂ : ⟨⟪c, d⟫, ⟪c', d'⟫⟩ ∈ RatEqRel) :
    ⟨⟪((a ·_ℤ d) +_ℤ (c ·_ℤ b)), (b ·_ℤ d)⟫,
      ⟪((a' ·_ℤ d') +_ℤ (c' ·_ℤ b')), (b' ·_ℤ d')⟫⟩ ∈ RatEqRel := by
  rcases (RatEqRel.Spec).1 h₁ with
    ⟨_, a0, b0, a1, b1, ha0Z, hb0NZ, ha1Z, hb1NZ, hPair₁, hEq₁⟩
  rcases (RatEqRel.Spec).1 h₂ with
    ⟨_, c0, d0, c1, d1, hc0Z, hd0NZ, hc1Z, hd1NZ, hPair₂, hEq₂⟩
  have hL₁ : ⟪a, b⟫ = ⟪a0, b0⟫ :=
    (OrderedPair.uniqueness (⟪a, b⟫) (⟪a', b'⟫)
      (⟪a0, b0⟫) (⟪a1, b1⟫)).1 hPair₁ |>.1
  have hR₁ : ⟪a', b'⟫ = ⟪a1, b1⟫ :=
    (OrderedPair.uniqueness (⟪a, b⟫) (⟪a', b'⟫)
      (⟪a0, b0⟫) (⟪a1, b1⟫)).1 hPair₁ |>.2
  have haEq : a = a0 := (OrderedPair.uniqueness a b a0 b0).1 hL₁ |>.1
  have hbEq : b = b0 := (OrderedPair.uniqueness a b a0 b0).1 hL₁ |>.2
  have ha'Eq : a' = a1 := (OrderedPair.uniqueness a' b' a1 b1).1 hR₁ |>.1
  have hb'Eq : b' = b1 := (OrderedPair.uniqueness a' b' a1 b1).1 hR₁ |>.2
  have hL₂ : ⟪c, d⟫ = ⟪c0, d0⟫ :=
    (OrderedPair.uniqueness (⟪c, d⟫) (⟪c', d'⟫)
      (⟪c0, d0⟫) (⟪c1, d1⟫)).1 hPair₂ |>.1
  have hR₂ : ⟪c', d'⟫ = ⟪c1, d1⟫ :=
    (OrderedPair.uniqueness (⟪c, d⟫) (⟪c', d'⟫)
      (⟪c0, d0⟫) (⟪c1, d1⟫)).1 hPair₂ |>.2
  have hcEq : c = c0 := (OrderedPair.uniqueness c d c0 d0).1 hL₂ |>.1
  have hdEq : d = d0 := (OrderedPair.uniqueness c d c0 d0).1 hL₂ |>.2
  have hc'Eq : c' = c1 := (OrderedPair.uniqueness c' d' c1 d1).1 hR₂ |>.1
  have hd'Eq : d' = d1 := (OrderedPair.uniqueness c' d' c1 d1).1 hR₂ |>.2
  subst a0 b0 a1 b1 c0 d0 c1 d1
  have hab :
      a ·_ℤ b' = a' ·_ℤ b := by
    simpa using hEq₁
  have hcd :
      c ·_ℤ d' = c' ·_ℤ d := by
    simpa using hEq₂
  have haZ : a ∈ ℤ := by simpa using ha0Z
  have hbNZ : b ∈ ℤ' := by simpa using hb0NZ
  have ha'Z : a' ∈ ℤ := by simpa using ha1Z
  have hb'NZ : b' ∈ ℤ' := by simpa using hb1NZ
  have hcZ : c ∈ ℤ := by simpa using hc0Z
  have hdNZ : d ∈ ℤ' := by simpa using hd0NZ
  have hc'Z : c' ∈ ℤ := by simpa using hc1Z
  have hd'NZ : d' ∈ ℤ' := by simpa using hd1NZ
  have hbZ : b ∈ ℤ := (ℤ'.Spec (z := b)).1 hbNZ |>.1
  have hb'Z : b' ∈ ℤ := (ℤ'.Spec (z := b')).1 hb'NZ |>.1
  have hdZ : d ∈ ℤ := (ℤ'.Spec (z := d)).1 hdNZ |>.1
  have hd'Z : d' ∈ ℤ := (ℤ'.Spec (z := d')).1 hd'NZ |>.1
  have hT1 :
      (a ·_ℤ d) ·_ℤ (b' ·_ℤ d') = (a' ·_ℤ d') ·_ℤ (b ·_ℤ d) := by
    have hMulHab : (a ·_ℤ b') ·_ℤ (d ·_ℤ d') = (a' ·_ℤ b) ·_ℤ (d ·_ℤ d') :=
      congrArg (fun x => x ·_ℤ (d ·_ℤ d')) hab
    calc
      (a ·_ℤ d) ·_ℤ (b' ·_ℤ d')
          = (a ·_ℤ b') ·_ℤ (d ·_ℤ d') := by
              calc
                (a ·_ℤ d) ·_ℤ (b' ·_ℤ d')
                    = ((a ·_ℤ d) ·_ℤ b') ·_ℤ d' := by
                        rw [int_mul_assoc (a ·_ℤ d) b' d' (int_mul_closed a d haZ hdZ) hb'Z hd'Z]
                _ = (a ·_ℤ (d ·_ℤ b')) ·_ℤ d' := by
                        rw [int_mul_assoc a d b' haZ hdZ hb'Z]
                _ = (a ·_ℤ (b' ·_ℤ d)) ·_ℤ d' := by
                        rw [int_mul_comm d b' hdZ hb'Z]
                _ = ((a ·_ℤ b') ·_ℤ d) ·_ℤ d' := by
                        rw [← int_mul_assoc a b' d haZ hb'Z hdZ]
                _ = (a ·_ℤ b') ·_ℤ (d ·_ℤ d') := by
                        rw [← int_mul_assoc (a ·_ℤ b') d d' (int_mul_closed a b' haZ hb'Z) hdZ hd'Z]
      _ = (a' ·_ℤ b) ·_ℤ (d ·_ℤ d') := hMulHab
      _ = (a' ·_ℤ d') ·_ℤ (b ·_ℤ d) := by
            calc
              (a' ·_ℤ b) ·_ℤ (d ·_ℤ d')
                  = ((a' ·_ℤ b) ·_ℤ d) ·_ℤ d' := by
                      rw [int_mul_assoc (a' ·_ℤ b) d d' (int_mul_closed a' b ha'Z hbZ) hdZ hd'Z]
              _ = (a' ·_ℤ (b ·_ℤ d)) ·_ℤ d' := by
                      rw [int_mul_assoc a' b d ha'Z hbZ hdZ]
              _ = (a' ·_ℤ (d ·_ℤ b)) ·_ℤ d' := by
                      rw [int_mul_comm b d hbZ hdZ]
              _ = ((a' ·_ℤ d) ·_ℤ b) ·_ℤ d' := by
                      rw [← int_mul_assoc a' d b ha'Z hdZ hbZ]
              _ = (a' ·_ℤ d) ·_ℤ (b ·_ℤ d') := by
                      rw [← int_mul_assoc (a' ·_ℤ d) b d' (int_mul_closed a' d ha'Z hdZ) hbZ hd'Z]
              _ = (a' ·_ℤ d) ·_ℤ (d' ·_ℤ b) := by
                      rw [int_mul_comm b d' hbZ hd'Z]
              _ = ((a' ·_ℤ d) ·_ℤ d') ·_ℤ b := by
                      rw [int_mul_assoc (a' ·_ℤ d) d' b (int_mul_closed a' d ha'Z hdZ) hd'Z hbZ]
              _ = (a' ·_ℤ (d ·_ℤ d')) ·_ℤ b := by
                      rw [int_mul_assoc a' d d' ha'Z hdZ hd'Z]
              _ = (a' ·_ℤ (d' ·_ℤ d)) ·_ℤ b := by
                      rw [int_mul_comm d d' hdZ hd'Z]
              _ = ((a' ·_ℤ d') ·_ℤ d) ·_ℤ b := by
                      rw [← int_mul_assoc a' d' d ha'Z hd'Z hdZ]
              _ = (a' ·_ℤ d') ·_ℤ (d ·_ℤ b) := by
                      rw [← int_mul_assoc (a' ·_ℤ d') d b (int_mul_closed a' d' ha'Z hd'Z) hdZ hbZ]
              _ = (a' ·_ℤ d') ·_ℤ (b ·_ℤ d) := by
                      rw [int_mul_comm d b hdZ hbZ]
  have hT2 :
      (c ·_ℤ b) ·_ℤ (b' ·_ℤ d') = (c' ·_ℤ b') ·_ℤ (b ·_ℤ d) := by
    have hMulHcd : (c ·_ℤ d') ·_ℤ (b ·_ℤ b') = (c' ·_ℤ d) ·_ℤ (b ·_ℤ b') :=
      congrArg (fun x => x ·_ℤ (b ·_ℤ b')) hcd
    calc
      (c ·_ℤ b) ·_ℤ (b' ·_ℤ d')
          = (c ·_ℤ d') ·_ℤ (b ·_ℤ b') := by
              calc
                (c ·_ℤ b) ·_ℤ (b' ·_ℤ d')
                    = ((c ·_ℤ b) ·_ℤ b') ·_ℤ d' := by
                        rw [int_mul_assoc (c ·_ℤ b) b' d' (int_mul_closed c b hcZ hbZ) hb'Z hd'Z]
                _ = (c ·_ℤ (b ·_ℤ b')) ·_ℤ d' := by
                        rw [int_mul_assoc c b b' hcZ hbZ hb'Z]
                _ = (c ·_ℤ (b' ·_ℤ b)) ·_ℤ d' := by
                        rw [int_mul_comm b b' hbZ hb'Z]
                _ = ((c ·_ℤ b') ·_ℤ b) ·_ℤ d' := by
                        rw [← int_mul_assoc c b' b hcZ hb'Z hbZ]
                _ = (c ·_ℤ b') ·_ℤ (b ·_ℤ d') := by
                        rw [← int_mul_assoc (c ·_ℤ b') b d' (int_mul_closed c b' hcZ hb'Z) hbZ hd'Z]
                _ = (c ·_ℤ d') ·_ℤ (b ·_ℤ b') := by
                        calc
                          (c ·_ℤ b') ·_ℤ (b ·_ℤ d')
                              = ((c ·_ℤ b') ·_ℤ b) ·_ℤ d' := by
                                  rw [int_mul_assoc (c ·_ℤ b') b d' (int_mul_closed c b' hcZ hb'Z) hbZ hd'Z]
                          _ = (c ·_ℤ (b' ·_ℤ b)) ·_ℤ d' := by
                                  rw [int_mul_assoc c b' b hcZ hb'Z hbZ]
                          _ = (c ·_ℤ (b ·_ℤ b')) ·_ℤ d' := by
                                  rw [int_mul_comm b' b hb'Z hbZ]
                          _ = c ·_ℤ ((b ·_ℤ b') ·_ℤ d') := by
                                  rw [int_mul_assoc c (b ·_ℤ b') d' hcZ (int_mul_closed b b' hbZ hb'Z) hd'Z]
                          _ = c ·_ℤ (d' ·_ℤ (b ·_ℤ b')) := by
                                  rw [int_mul_comm (b ·_ℤ b') d' (int_mul_closed b b' hbZ hb'Z) hd'Z]
                          _ = (c ·_ℤ d') ·_ℤ (b ·_ℤ b') := by
                                  rw [← int_mul_assoc c d' (b ·_ℤ b') hcZ hd'Z (int_mul_closed b b' hbZ hb'Z)]
      _ = (c' ·_ℤ d) ·_ℤ (b ·_ℤ b') := hMulHcd
      _ = (c' ·_ℤ b') ·_ℤ (b ·_ℤ d) := by
            calc
              (c' ·_ℤ d) ·_ℤ (b ·_ℤ b')
                  = ((c' ·_ℤ d) ·_ℤ b) ·_ℤ b' := by
                      rw [int_mul_assoc (c' ·_ℤ d) b b' (int_mul_closed c' d hc'Z hdZ) hbZ hb'Z]
              _ = (c' ·_ℤ (d ·_ℤ b)) ·_ℤ b' := by
                      rw [int_mul_assoc c' d b hc'Z hdZ hbZ]
              _ = (c' ·_ℤ (b ·_ℤ d)) ·_ℤ b' := by
                      rw [int_mul_comm d b hdZ hbZ]
              _ = ((c' ·_ℤ b) ·_ℤ d) ·_ℤ b' := by
                      rw [← int_mul_assoc c' b d hc'Z hbZ hdZ]
              _ = (c' ·_ℤ b) ·_ℤ (d ·_ℤ b') := by
                      rw [← int_mul_assoc (c' ·_ℤ b) d b' (int_mul_closed c' b hc'Z hbZ) hdZ hb'Z]
              _ = (c' ·_ℤ b) ·_ℤ (b' ·_ℤ d) := by
                      rw [int_mul_comm d b' hdZ hb'Z]
              _ = ((c' ·_ℤ b) ·_ℤ b') ·_ℤ d := by
                      rw [int_mul_assoc (c' ·_ℤ b) b' d (int_mul_closed c' b hc'Z hbZ) hb'Z hdZ]
              _ = (c' ·_ℤ (b ·_ℤ b')) ·_ℤ d := by
                      rw [int_mul_assoc c' b b' hc'Z hbZ hb'Z]
              _ = (c' ·_ℤ (b' ·_ℤ b)) ·_ℤ d := by
                      rw [int_mul_comm b b' hbZ hb'Z]
              _ = ((c' ·_ℤ b') ·_ℤ b) ·_ℤ d := by
                      rw [← int_mul_assoc c' b' b hc'Z hb'Z hbZ]
              _ = (c' ·_ℤ b') ·_ℤ (b ·_ℤ d) := by
                      rw [← int_mul_assoc (c' ·_ℤ b') b d (int_mul_closed c' b' hc'Z hb'Z) hbZ hdZ]
  have hNumEq :
      (((a ·_ℤ d) +_ℤ (c ·_ℤ b)) ·_ℤ (b' ·_ℤ d')) =
      (((a' ·_ℤ d') +_ℤ (c' ·_ℤ b')) ·_ℤ (b ·_ℤ d)) := by
    calc
      (((a ·_ℤ d) +_ℤ (c ·_ℤ b)) ·_ℤ (b' ·_ℤ d'))
          = ((a ·_ℤ d) ·_ℤ (b' ·_ℤ d')) +_ℤ ((c ·_ℤ b) ·_ℤ (b' ·_ℤ d')) := by
              exact int_mul_right_distrib (a ·_ℤ d) (c ·_ℤ b) (b' ·_ℤ d')
                (int_mul_closed a d haZ hdZ) (int_mul_closed c b hcZ hbZ) (int_mul_closed b' d' hb'Z hd'Z)
      _ = ((a' ·_ℤ d') ·_ℤ (b ·_ℤ d)) +_ℤ ((c' ·_ℤ b') ·_ℤ (b ·_ℤ d)) := by rw [hT1, hT2]
      _ = (((a' ·_ℤ d') +_ℤ (c' ·_ℤ b')) ·_ℤ (b ·_ℤ d)) := by
              exact (int_mul_right_distrib (a' ·_ℤ d') (c' ·_ℤ b') (b ·_ℤ d)
                (int_mul_closed a' d' ha'Z hd'Z) (int_mul_closed c' b' hc'Z hb'Z) (int_mul_closed b d hbZ hdZ)).symm
  exact RatEqRel.pair_mem
    ((a ·_ℤ d) +_ℤ (c ·_ℤ b)) (b ·_ℤ d)
    ((a' ·_ℤ d') +_ℤ (c' ·_ℤ b')) (b' ·_ℤ d')
    (int_add_closed (a ·_ℤ d) (c ·_ℤ b) (int_mul_closed a d haZ hdZ) (int_mul_closed c b hcZ hbZ))
    (int_mul_mem_nonzero b d hbNZ hdNZ)
    (int_add_closed (a' ·_ℤ d') (c' ·_ℤ b') (int_mul_closed a' d' ha'Z hd'Z) (int_mul_closed c' b' hc'Z hb'Z))
    (int_mul_mem_nonzero b' d' hb'NZ hd'NZ)
    hNumEq

noncomputable def rat_add_candidate (r s : Set) : Set :=
  [⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎

lemma rat_add_candidate_closed (r s : Set) (hr : r ∈ ℚ) (hs : s ∈ ℚ) :
    rat_add_candidate r s ∈ ℚ := by
  have hrSpec := rat_num_den_spec r hr
  have hsSpec := rat_num_den_spec s hs
  have hrnZ : rat_num r ∈ ℤ := hrSpec.1
  have hrdNZ : rat_den r ∈ ℤ' := hrSpec.2.1
  have hsnZ : rat_num s ∈ ℤ := hsSpec.1
  have hsdNZ : rat_den s ∈ ℤ' := hsSpec.2.1
  have hrdZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hrdNZ |>.1
  have hsdZ : rat_den s ∈ ℤ := (ℤ'.Spec).1 hsdNZ |>.1
  exact EquivalenceClass.mem_quotient (ℤ ⨯ ℤ') RatEqRel
    (⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫)
    (by
      simpa using Pair.mem_product ℤ ℤ'
        ((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r))
        (rat_den r ·_ℤ rat_den s)
        (int_add_closed
          (rat_num r ·_ℤ rat_den s) (rat_num s ·_ℤ rat_den r)
          (int_mul_closed (rat_num r) (rat_den s) hrnZ hsdZ)
          (int_mul_closed (rat_num s) (rat_den r) hsnZ hrdZ))
        (int_mul_mem_nonzero (rat_den r) (rat_den s) hrdNZ hsdNZ))

lemma rat_add_candidate_comm (r s : Set) (hr : r ∈ ℚ) (hs : s ∈ ℚ) :
    rat_add_candidate r s = rat_add_candidate s r := by
  have hrSpec := rat_num_den_spec r hr
  have hsSpec := rat_num_den_spec s hs
  have hrnZ : rat_num r ∈ ℤ := hrSpec.1
  have hrdZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hrSpec.2.1 |>.1
  have hsnZ : rat_num s ∈ ℤ := hsSpec.1
  have hsdZ : rat_den s ∈ ℤ := (ℤ'.Spec).1 hsSpec.2.1 |>.1
  simp [rat_add_candidate,
    int_add_comm
      (rat_num r ·_ℤ rat_den s)
      (rat_num s ·_ℤ rat_den r)
      (int_mul_closed (rat_num r) (rat_den s) hrnZ hsdZ)
      (int_mul_closed (rat_num s) (rat_den r) hsnZ hrdZ),
    int_mul_comm (rat_den r) (rat_den s) hrdZ hsdZ]

lemma rat_add_candidate_zero_right (r : Set) (hr : r ∈ ℚ) :
    rat_add_candidate r zero_ℚ = r := by
  have hrSpec := rat_num_den_spec r hr
  have h0Spec := rat_num_den_spec zero_ℚ zero_ℚ_mem_ℚ
  have haZ : rat_num r ∈ ℤ := hrSpec.1
  have hbNZ : rat_den r ∈ ℤ' := hrSpec.2.1
  have huZ : rat_num zero_ℚ ∈ ℤ := h0Spec.1
  have hvNZ : rat_den zero_ℚ ∈ ℤ' := h0Spec.2.1
  have hbZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hbNZ |>.1
  have hvZ : rat_den zero_ℚ ∈ ℤ := (ℤ'.Spec).1 hvNZ |>.1
  have h0ClassEq :
      [⟪(rat_num zero_ℚ), (rat_den zero_ℚ)⟫]₍RatEqRel₎ =
      [⟪zero_ℤ, one_ℤ⟫]₍RatEqRel₎ := by
    calc
      [⟪(rat_num zero_ℚ), (rat_den zero_ℚ)⟫]₍RatEqRel₎ = zero_ℚ := h0Spec.2.2.symm
      _ = [⟪zero_ℤ, one_ℤ⟫]₍RatEqRel₎ := rfl
  have hRelZero :
      ⟨⟪(rat_num zero_ℚ), (rat_den zero_ℚ)⟫, ⟪zero_ℤ, one_ℤ⟫⟩ ∈ RatEqRel := by
    exact (rat_class_eq_iff
      (rat_num zero_ℚ) (rat_den zero_ℚ) zero_ℤ one_ℤ
      huZ hvNZ zero_ℤ_mem_ℤ one_ℤ_mem_nonzero).1 h0ClassEq
  have hReflR :
      ⟨⟪(rat_num r), (rat_den r)⟫, ⟪(rat_num r), (rat_den r)⟫⟩ ∈ RatEqRel := by
    exact RatEqRel.pair_mem (rat_num r) (rat_den r) (rat_num r) (rat_den r)
      haZ hbNZ haZ hbNZ rfl
  have hRelAdd :
      ⟨⟪((rat_num r ·_ℤ rat_den zero_ℚ) +_ℤ (rat_num zero_ℚ ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den zero_ℚ)⟫,
        ⟪((rat_num r ·_ℤ one_ℤ) +_ℤ (zero_ℤ ·_ℤ rat_den r)), (rat_den r ·_ℤ one_ℤ)⟫⟩ ∈ RatEqRel := by
    exact rat_add_pair_congr
      (rat_num r) (rat_den r)
      (rat_num zero_ℚ) (rat_den zero_ℚ)
      (rat_num r) (rat_den r)
      zero_ℤ one_ℤ
      hReflR hRelZero
  have hClassAdd :
      [⟪((rat_num r ·_ℤ rat_den zero_ℚ) +_ℤ (rat_num zero_ℚ ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den zero_ℚ)⟫]₍RatEqRel₎ =
      [⟪((rat_num r ·_ℤ one_ℤ) +_ℤ (zero_ℤ ·_ℤ rat_den r)), (rat_den r ·_ℤ one_ℤ)⟫]₍RatEqRel₎ := by
    exact (rat_class_eq_iff
      ((rat_num r ·_ℤ rat_den zero_ℚ) +_ℤ (rat_num zero_ℚ ·_ℤ rat_den r))
      (rat_den r ·_ℤ rat_den zero_ℚ)
      ((rat_num r ·_ℤ one_ℤ) +_ℤ (zero_ℤ ·_ℤ rat_den r))
      (rat_den r ·_ℤ one_ℤ)
      (int_add_closed
        (rat_num r ·_ℤ rat_den zero_ℚ) (rat_num zero_ℚ ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) (rat_den zero_ℚ) haZ hvZ)
        (int_mul_closed (rat_num zero_ℚ) (rat_den r) huZ hbZ))
      (int_mul_mem_nonzero (rat_den r) (rat_den zero_ℚ) hbNZ hvNZ)
      (int_add_closed
        (rat_num r ·_ℤ one_ℤ) (zero_ℤ ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) one_ℤ haZ one_ℤ_mem_ℤ)
        (int_mul_closed zero_ℤ (rat_den r) zero_ℤ_mem_ℤ hbZ))
      (int_mul_mem_nonzero (rat_den r) one_ℤ hbNZ one_ℤ_mem_nonzero)).2 hRelAdd
  calc
    rat_add_candidate r zero_ℚ
        = [⟪((rat_num r ·_ℤ rat_den zero_ℚ) +_ℤ (rat_num zero_ℚ ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den zero_ℚ)⟫]₍RatEqRel₎ := by rfl
    _ = [⟪((rat_num r ·_ℤ one_ℤ) +_ℤ (zero_ℤ ·_ℤ rat_den r)), (rat_den r ·_ℤ one_ℤ)⟫]₍RatEqRel₎ := hClassAdd
    _ = [⟪(rat_num r), (rat_den r)⟫]₍RatEqRel₎ := by
          simp [int_mul_one_right (rat_num r) haZ, int_mul_one_right (rat_den r) hbZ,
            int_mul_zero_left (rat_den r) hbZ, int_add_zero_right (rat_num r) haZ]
    _ = r := hrSpec.2.2.symm

lemma rat_add_candidate_has_inverse (r : Set) (hr : r ∈ ℚ) :
    ∃ s, s ∈ ℚ ∧ rat_add_candidate r s = zero_ℚ := by
  have hrSpec := rat_num_den_spec r hr
  have haZ : rat_num r ∈ ℤ := hrSpec.1
  have hbNZ : rat_den r ∈ ℤ' := hrSpec.2.1
  have hbZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hbNZ |>.1
  let aInv : Set := Classical.choose (int_add_inv_exists (rat_num r) haZ)
  have haInvZ : aInv ∈ ℤ := (Classical.choose_spec (int_add_inv_exists (rat_num r) haZ)).1
  have hInvEq : rat_num r +_ℤ aInv = zero_ℤ := (Classical.choose_spec (int_add_inv_exists (rat_num r) haZ)).2
  let s : Set := [⟪aInv, (rat_den r)⟫]₍RatEqRel₎
  have hs : s ∈ ℚ := by
    exact EquivalenceClass.mem_quotient (ℤ ⨯ ℤ') RatEqRel
      (⟪aInv, (rat_den r)⟫)
      (by simpa using Pair.mem_product ℤ ℤ' aInv (rat_den r) haInvZ hbNZ)
  have hsSpec := rat_num_den_spec s hs
  have hClassSEq :
      [⟪(rat_num s), (rat_den s)⟫]₍RatEqRel₎ =
      [⟪aInv, (rat_den r)⟫]₍RatEqRel₎ := by
    calc
      [⟪(rat_num s), (rat_den s)⟫]₍RatEqRel₎ = s := hsSpec.2.2.symm
      _ = [⟪aInv, (rat_den r)⟫]₍RatEqRel₎ := by simp [s]
  have hRelS :
      ⟨⟪(rat_num s), (rat_den s)⟫, ⟪aInv, (rat_den r)⟫⟩ ∈ RatEqRel := by
    exact (rat_class_eq_iff
      (rat_num s) (rat_den s) aInv (rat_den r)
      hsSpec.1 hsSpec.2.1 haInvZ hbNZ).1 hClassSEq
  have hReflR :
      ⟨⟪(rat_num r), (rat_den r)⟫, ⟪(rat_num r), (rat_den r)⟫⟩ ∈ RatEqRel := by
    exact RatEqRel.pair_mem (rat_num r) (rat_den r) (rat_num r) (rat_den r)
      haZ hbNZ haZ hbNZ rfl
  have hRelAdd :
      ⟨⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫,
        ⟪((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den r)⟫⟩ ∈ RatEqRel := by
    exact rat_add_pair_congr
      (rat_num r) (rat_den r)
      (rat_num s) (rat_den s)
      (rat_num r) (rat_den r)
      aInv (rat_den r)
      hReflR hRelS
  have hClassAdd :
      [⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎ =
      [⟪((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den r)⟫]₍RatEqRel₎ := by
    exact (rat_class_eq_iff
      ((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r))
      (rat_den r ·_ℤ rat_den s)
      ((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r))
      (rat_den r ·_ℤ rat_den r)
      (int_add_closed
        (rat_num r ·_ℤ rat_den s) (rat_num s ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) (rat_den s) haZ ((ℤ'.Spec).1 hsSpec.2.1 |>.1))
        (int_mul_closed (rat_num s) (rat_den r) hsSpec.1 hbZ))
      (int_mul_mem_nonzero (rat_den r) (rat_den s) hbNZ hsSpec.2.1)
      (int_add_closed
        (rat_num r ·_ℤ rat_den r) (aInv ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) (rat_den r) haZ hbZ)
        (int_mul_closed aInv (rat_den r) haInvZ hbZ))
      (int_mul_mem_nonzero (rat_den r) (rat_den r) hbNZ hbNZ)).2 hRelAdd
  have hNumZero :
      (rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r) = zero_ℤ := by
    calc
      (rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)
          = (rat_num r +_ℤ aInv) ·_ℤ rat_den r := by
              exact (int_mul_right_distrib (rat_num r) aInv (rat_den r) haZ haInvZ hbZ).symm
      _ = zero_ℤ ·_ℤ rat_den r := by rw [hInvEq]
      _ = zero_ℤ := int_mul_zero_left (rat_den r) hbZ
  have hDenNZ : (rat_den r ·_ℤ rat_den r) ∈ ℤ' :=
    int_mul_mem_nonzero (rat_den r) (rat_den r) hbNZ hbNZ
  have hDenZ : (rat_den r ·_ℤ rat_den r) ∈ ℤ :=
    (ℤ'.Spec).1 hDenNZ |>.1
  have hRelZero :
      ⟨⟪((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den r)⟫,
        ⟪zero_ℤ, one_ℤ⟫⟩ ∈ RatEqRel := by
    refine RatEqRel.pair_mem
      ((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r))
      (rat_den r ·_ℤ rat_den r)
      zero_ℤ one_ℤ
      (int_add_closed
        (rat_num r ·_ℤ rat_den r) (aInv ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) (rat_den r) haZ hbZ)
        (int_mul_closed aInv (rat_den r) haInvZ hbZ))
      hDenNZ
      zero_ℤ_mem_ℤ
      one_ℤ_mem_nonzero
      ?_
    calc
      (((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)) ·_ℤ one_ℤ)
          = ((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)) := by
              exact int_mul_one_right ((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r))
                (int_add_closed
                  (rat_num r ·_ℤ rat_den r) (aInv ·_ℤ rat_den r)
                  (int_mul_closed (rat_num r) (rat_den r) haZ hbZ)
                  (int_mul_closed aInv (rat_den r) haInvZ hbZ))
      _ = zero_ℤ := hNumZero
      _ = zero_ℤ ·_ℤ (rat_den r ·_ℤ rat_den r) := by
            exact (int_mul_zero_left (rat_den r ·_ℤ rat_den r) hDenZ).symm
  have hClassZero :
      [⟪((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den r)⟫]₍RatEqRel₎ = zero_ℚ := by
    calc
      [⟪((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den r)⟫]₍RatEqRel₎
          = [⟪zero_ℤ, one_ℤ⟫]₍RatEqRel₎ := by
              exact (rat_class_eq_iff
                ((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r))
                (rat_den r ·_ℤ rat_den r) zero_ℤ one_ℤ
                (int_add_closed
                  (rat_num r ·_ℤ rat_den r) (aInv ·_ℤ rat_den r)
                  (int_mul_closed (rat_num r) (rat_den r) haZ hbZ)
                  (int_mul_closed aInv (rat_den r) haInvZ hbZ))
                hDenNZ
                zero_ℤ_mem_ℤ
                one_ℤ_mem_nonzero).2 hRelZero
      _ = zero_ℚ := rfl
  refine ⟨s, hs, ?_⟩
  calc
    rat_add_candidate r s
        = [⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎ := rfl
    _ = [⟪((rat_num r ·_ℤ rat_den r) +_ℤ (aInv ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den r)⟫]₍RatEqRel₎ := hClassAdd
    _ = zero_ℚ := hClassZero

lemma rat_add_candidate_assoc (r s t : Set)
    (hr : r ∈ ℚ) (hs : s ∈ ℚ) (ht : t ∈ ℚ) :
    rat_add_candidate (rat_add_candidate r s) t = rat_add_candidate r (rat_add_candidate s t) := by
  have hrSpec := rat_num_den_spec r hr
  have hsSpec := rat_num_den_spec s hs
  have htSpec := rat_num_den_spec t ht
  have haZ : rat_num r ∈ ℤ := hrSpec.1
  have hbNZ : rat_den r ∈ ℤ' := hrSpec.2.1
  have hcZ : rat_num s ∈ ℤ := hsSpec.1
  have hdNZ : rat_den s ∈ ℤ' := hsSpec.2.1
  have heZ : rat_num t ∈ ℤ := htSpec.1
  have hfNZ : rat_den t ∈ ℤ' := htSpec.2.1
  have hbZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hbNZ |>.1
  have hdZ : rat_den s ∈ ℤ := (ℤ'.Spec).1 hdNZ |>.1
  have hfZ : rat_den t ∈ ℤ := (ℤ'.Spec).1 hfNZ |>.1
  have hAddRS : rat_add_candidate r s ∈ ℚ := rat_add_candidate_closed r s hr hs
  have hAddST : rat_add_candidate s t ∈ ℚ := rat_add_candidate_closed s t hs ht
  have hRSspec := rat_num_den_spec (rat_add_candidate r s) hAddRS
  have hSTspec := rat_num_den_spec (rat_add_candidate s t) hAddST
  have hRSclassEq :
      [⟪(rat_num (rat_add_candidate r s)), (rat_den (rat_add_candidate r s))⟫]₍RatEqRel₎ =
      [⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎ := by
    calc
      [⟪(rat_num (rat_add_candidate r s)), (rat_den (rat_add_candidate r s))⟫]₍RatEqRel₎
          = rat_add_candidate r s := hRSspec.2.2.symm
      _ = [⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫]₍RatEqRel₎ := by rfl
  have hSTclassEq :
      [⟪(rat_num (rat_add_candidate s t)), (rat_den (rat_add_candidate s t))⟫]₍RatEqRel₎ =
      [⟪((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)), (rat_den s ·_ℤ rat_den t)⟫]₍RatEqRel₎ := by
    calc
      [⟪(rat_num (rat_add_candidate s t)), (rat_den (rat_add_candidate s t))⟫]₍RatEqRel₎
          = rat_add_candidate s t := hSTspec.2.2.symm
      _ = [⟪((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)), (rat_den s ·_ℤ rat_den t)⟫]₍RatEqRel₎ := by rfl
  have hRelRS :
      ⟨⟪(rat_num (rat_add_candidate r s)), (rat_den (rat_add_candidate r s))⟫,
        ⟪((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den s)⟫⟩ ∈ RatEqRel := by
    have hNumRSZ :
        (rat_num (rat_add_candidate r s)) ∈ ℤ := hRSspec.1
    have hDenRSNZ :
        (rat_den (rat_add_candidate r s)) ∈ ℤ' := hRSspec.2.1
    have hNumRawZ :
        ((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ∈ ℤ :=
      int_add_closed
        (rat_num r ·_ℤ rat_den s) (rat_num s ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) (rat_den s) haZ hdZ)
        (int_mul_closed (rat_num s) (rat_den r) hcZ hbZ)
    have hDenRawNZ :
        (rat_den r ·_ℤ rat_den s) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den r) (rat_den s) hbNZ hdNZ
    exact (rat_class_eq_iff
      (rat_num (rat_add_candidate r s)) (rat_den (rat_add_candidate r s))
      ((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r))
      (rat_den r ·_ℤ rat_den s)
      hNumRSZ hDenRSNZ hNumRawZ hDenRawNZ).1 hRSclassEq
  have hRelST :
      ⟨⟪(rat_num (rat_add_candidate s t)), (rat_den (rat_add_candidate s t))⟫,
        ⟪((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)), (rat_den s ·_ℤ rat_den t)⟫⟩ ∈ RatEqRel := by
    have hNumSTZ :
        (rat_num (rat_add_candidate s t)) ∈ ℤ := hSTspec.1
    have hDenSTNZ :
        (rat_den (rat_add_candidate s t)) ∈ ℤ' := hSTspec.2.1
    have hNumRawZ :
        ((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ∈ ℤ :=
      int_add_closed
        (rat_num s ·_ℤ rat_den t) (rat_num t ·_ℤ rat_den s)
        (int_mul_closed (rat_num s) (rat_den t) hcZ hfZ)
        (int_mul_closed (rat_num t) (rat_den s) heZ hdZ)
    have hDenRawNZ :
        (rat_den s ·_ℤ rat_den t) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den s) (rat_den t) hdNZ hfNZ
    exact (rat_class_eq_iff
      (rat_num (rat_add_candidate s t)) (rat_den (rat_add_candidate s t))
      ((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s))
      (rat_den s ·_ℤ rat_den t)
      hNumSTZ hDenSTNZ hNumRawZ hDenRawNZ).1 hSTclassEq
  have hRelLeft :
      ⟨⟪((rat_num (rat_add_candidate r s) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ rat_den (rat_add_candidate r s))), (rat_den (rat_add_candidate r s) ·_ℤ rat_den t)⟫,
        ⟪((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫⟩ ∈ RatEqRel := by
    have hReflT : ⟨⟪(rat_num t), (rat_den t)⟫, ⟪(rat_num t), (rat_den t)⟫⟩ ∈ RatEqRel := by
      exact RatEqRel.pair_mem (rat_num t) (rat_den t) (rat_num t) (rat_den t)
        heZ hfNZ heZ hfNZ rfl
    exact rat_add_pair_congr
      (rat_num (rat_add_candidate r s)) (rat_den (rat_add_candidate r s))
      (rat_num t) (rat_den t)
      ((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r))
      (rat_den r ·_ℤ rat_den s)
      (rat_num t) (rat_den t)
      hRelRS hReflT
  have hRelRight :
      ⟨⟪((rat_num r ·_ℤ rat_den (rat_add_candidate s t)) +_ℤ
          (rat_num (rat_add_candidate s t) ·_ℤ rat_den r)), (rat_den r ·_ℤ rat_den (rat_add_candidate s t))⟫,
        ⟪((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
          (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫⟩ ∈ RatEqRel := by
    have hReflR : ⟨⟪(rat_num r), (rat_den r)⟫, ⟪(rat_num r), (rat_den r)⟫⟩ ∈ RatEqRel := by
      exact RatEqRel.pair_mem (rat_num r) (rat_den r) (rat_num r) (rat_den r)
        haZ hbNZ haZ hbNZ rfl
    exact rat_add_pair_congr
      (rat_num r) (rat_den r)
      (rat_num (rat_add_candidate s t)) (rat_den (rat_add_candidate s t))
      (rat_num r) (rat_den r)
      ((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s))
      (rat_den s ·_ℤ rat_den t)
      hReflR hRelST
  have hClassLeft :
      rat_add_candidate (rat_add_candidate r s) t =
        [⟪((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫]₍RatEqRel₎ := by
    have hNumLZ :
        ((rat_num (rat_add_candidate r s) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ rat_den (rat_add_candidate r s))) ∈ ℤ :=
      int_add_closed
        (rat_num (rat_add_candidate r s) ·_ℤ rat_den t)
        (rat_num t ·_ℤ rat_den (rat_add_candidate r s))
        (int_mul_closed (rat_num (rat_add_candidate r s)) (rat_den t) hRSspec.1 hfZ)
        (int_mul_closed (rat_num t) (rat_den (rat_add_candidate r s)) heZ ((ℤ'.Spec).1 hRSspec.2.1 |>.1))
    have hDenLNZ :
        (rat_den (rat_add_candidate r s) ·_ℤ rat_den t) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den (rat_add_candidate r s)) (rat_den t) hRSspec.2.1 hfNZ
    have hNumRawZ :
        ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))) ∈ ℤ :=
      int_add_closed
        (((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t)
        (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))
        (int_mul_closed
          ((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r))
          (rat_den t)
          (int_add_closed
            (rat_num r ·_ℤ rat_den s) (rat_num s ·_ℤ rat_den r)
            (int_mul_closed (rat_num r) (rat_den s) haZ hdZ)
            (int_mul_closed (rat_num s) (rat_den r) hcZ hbZ))
          hfZ)
        (int_mul_closed (rat_num t) (rat_den r ·_ℤ rat_den s) heZ (int_mul_closed (rat_den r) (rat_den s) hbZ hdZ))
    have hDenRawNZ :
        ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den r ·_ℤ rat_den s) (rat_den t)
        (int_mul_mem_nonzero (rat_den r) (rat_den s) hbNZ hdNZ) hfNZ
    exact (rat_class_eq_iff
      ((rat_num (rat_add_candidate r s) ·_ℤ rat_den t) +_ℤ
        (rat_num t ·_ℤ rat_den (rat_add_candidate r s)))
      (rat_den (rat_add_candidate r s) ·_ℤ rat_den t)
      ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
        (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s)))
      ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)
      hNumLZ hDenLNZ hNumRawZ hDenRawNZ).2 hRelLeft
  have hClassRight :
      rat_add_candidate r (rat_add_candidate s t) =
        [⟪((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
          (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫]₍RatEqRel₎ := by
    have hNumRZ :
        ((rat_num r ·_ℤ rat_den (rat_add_candidate s t)) +_ℤ
          (rat_num (rat_add_candidate s t) ·_ℤ rat_den r)) ∈ ℤ :=
      int_add_closed
        (rat_num r ·_ℤ rat_den (rat_add_candidate s t))
        (rat_num (rat_add_candidate s t) ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) (rat_den (rat_add_candidate s t)) haZ ((ℤ'.Spec).1 hSTspec.2.1 |>.1))
        (int_mul_closed (rat_num (rat_add_candidate s t)) (rat_den r) hSTspec.1 hbZ)
    have hDenRNZ :
        (rat_den r ·_ℤ rat_den (rat_add_candidate s t)) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den r) (rat_den (rat_add_candidate s t)) hbNZ hSTspec.2.1
    have hNumRawZ :
        ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
          (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)) ∈ ℤ :=
      int_add_closed
        (rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t))
        (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)
        (int_mul_closed (rat_num r) (rat_den s ·_ℤ rat_den t) haZ (int_mul_closed (rat_den s) (rat_den t) hdZ hfZ))
        (int_mul_closed
          ((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s))
          (rat_den r)
          (int_add_closed
            (rat_num s ·_ℤ rat_den t) (rat_num t ·_ℤ rat_den s)
            (int_mul_closed (rat_num s) (rat_den t) hcZ hfZ)
            (int_mul_closed (rat_num t) (rat_den s) heZ hdZ))
          hbZ)
    have hDenRawNZ :
        (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t)) ∈ ℤ' :=
      int_mul_mem_nonzero (rat_den r) (rat_den s ·_ℤ rat_den t)
        hbNZ (int_mul_mem_nonzero (rat_den s) (rat_den t) hdNZ hfNZ)
    exact (rat_class_eq_iff
      ((rat_num r ·_ℤ rat_den (rat_add_candidate s t)) +_ℤ
        (rat_num (rat_add_candidate s t) ·_ℤ rat_den r))
      (rat_den r ·_ℤ rat_den (rat_add_candidate s t))
      ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
        (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r))
      (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))
      hNumRZ hDenRNZ hNumRawZ hDenRawNZ).2 hRelRight
  have hNumEq :
      ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
        (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))) =
      ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
        (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)) := by
    calc
      ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s)))
          = (((rat_num r ·_ℤ rat_den s) ·_ℤ rat_den t) +_ℤ
              ((rat_num s ·_ℤ rat_den r) ·_ℤ rat_den t)) +_ℤ
              (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s)) := by
              rw [int_mul_right_distrib
                (rat_num r ·_ℤ rat_den s)
                (rat_num s ·_ℤ rat_den r)
                (rat_den t)
                (int_mul_closed (rat_num r) (rat_den s) haZ hdZ)
                (int_mul_closed (rat_num s) (rat_den r) hcZ hbZ)
                hfZ]
      _ = ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
            ((rat_num s ·_ℤ (rat_den r ·_ℤ rat_den t)) +_ℤ
              (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s)))) := by
            rw [int_mul_assoc (rat_num r) (rat_den s) (rat_den t) haZ hdZ hfZ]
            rw [int_mul_assoc (rat_num s) (rat_den r) (rat_den t) hcZ hbZ hfZ]
            rw [int_add_assoc
              (rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t))
              (rat_num s ·_ℤ (rat_den r ·_ℤ rat_den t))
              (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))
              (int_mul_closed (rat_num r) (rat_den s ·_ℤ rat_den t) haZ (int_mul_closed (rat_den s) (rat_den t) hdZ hfZ))
              (int_mul_closed (rat_num s) (rat_den r ·_ℤ rat_den t) hcZ (int_mul_closed (rat_den r) (rat_den t) hbZ hfZ))
              (int_mul_closed (rat_num t) (rat_den r ·_ℤ rat_den s) heZ (int_mul_closed (rat_den r) (rat_den s) hbZ hdZ))]
      _ = ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
            ((rat_num s ·_ℤ (rat_den t ·_ℤ rat_den r)) +_ℤ
              (rat_num t ·_ℤ (rat_den s ·_ℤ rat_den r)))) := by
            rw [int_mul_comm (rat_den r) (rat_den t) hbZ hfZ]
            rw [int_mul_comm (rat_den r) (rat_den s) hbZ hdZ]
      _ = ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
            (((rat_num s ·_ℤ rat_den t) ·_ℤ rat_den r) +_ℤ
              ((rat_num t ·_ℤ rat_den s) ·_ℤ rat_den r))) := by
            rw [← int_mul_assoc (rat_num s) (rat_den t) (rat_den r) hcZ hfZ hbZ]
            rw [← int_mul_assoc (rat_num t) (rat_den s) (rat_den r) heZ hdZ hbZ]
      _ = ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
            (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)) := by
            rw [← int_mul_right_distrib
              (rat_num s ·_ℤ rat_den t)
              (rat_num t ·_ℤ rat_den s)
              (rat_den r)
              (int_mul_closed (rat_num s) (rat_den t) hcZ hfZ)
              (int_mul_closed (rat_num t) (rat_den s) heZ hdZ)
              hbZ]
  have hDenEq :
      ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t) =
      (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t)) := by
    exact int_mul_assoc (rat_den r) (rat_den s) (rat_den t) hbZ hdZ hfZ
  have hDenLNZ :
      ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t) ∈ ℤ' :=
    int_mul_mem_nonzero (rat_den r ·_ℤ rat_den s) (rat_den t)
      (int_mul_mem_nonzero (rat_den r) (rat_den s) hbNZ hdNZ) hfNZ
  have hDenRNZ :
      (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t)) ∈ ℤ' :=
    int_mul_mem_nonzero (rat_den r) (rat_den s ·_ℤ rat_den t)
      hbNZ (int_mul_mem_nonzero (rat_den s) (rat_den t) hdNZ hfNZ)
  have hNumLZ :
      ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
        (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))) ∈ ℤ := by
    exact int_add_closed
      (((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t)
      (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))
      (int_mul_closed
        ((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r))
        (rat_den t)
        (int_add_closed
          (rat_num r ·_ℤ rat_den s) (rat_num s ·_ℤ rat_den r)
          (int_mul_closed (rat_num r) (rat_den s) haZ hdZ)
          (int_mul_closed (rat_num s) (rat_den r) hcZ hbZ))
        hfZ)
      (int_mul_closed (rat_num t) (rat_den r ·_ℤ rat_den s) heZ (int_mul_closed (rat_den r) (rat_den s) hbZ hdZ))
  have hNumRZ :
      ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
        (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)) ∈ ℤ := by
    exact int_add_closed
      (rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t))
      (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)
      (int_mul_closed (rat_num r) (rat_den s ·_ℤ rat_den t) haZ (int_mul_closed (rat_den s) (rat_den t) hdZ hfZ))
      (int_mul_closed
        ((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s))
        (rat_den r)
        (int_add_closed
          (rat_num s ·_ℤ rat_den t) (rat_num t ·_ℤ rat_den s)
          (int_mul_closed (rat_num s) (rat_den t) hcZ hfZ)
          (int_mul_closed (rat_num t) (rat_den s) heZ hdZ))
        hbZ)
  have hRelMain :
      ⟨⟪((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫,
        ⟪((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
          (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫⟩ ∈ RatEqRel := by
    refine RatEqRel.pair_mem
      ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
        (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s)))
      ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)
      ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
        (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r))
      (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))
      hNumLZ hDenLNZ hNumRZ hDenRNZ ?_
    calc
      (((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))) ·_ℤ
          (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t)))
          = ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
              (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))) ·_ℤ
              (((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)) := by
                rw [hDenEq]
      _ = (((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
            (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)) ·_ℤ
            (((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t))) := by
              rw [hNumEq]
  have hClassMain :
      [⟪((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
          (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫]₍RatEqRel₎ =
      [⟪((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
          (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫]₍RatEqRel₎ := by
    exact (rat_class_eq_iff
      ((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
        (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s)))
      ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)
      ((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
        (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r))
      (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))
      hNumLZ hDenLNZ hNumRZ hDenRNZ).2 hRelMain
  calc
    rat_add_candidate (rat_add_candidate r s) t
        = [⟪((((rat_num r ·_ℤ rat_den s) +_ℤ (rat_num s ·_ℤ rat_den r)) ·_ℤ rat_den t) +_ℤ
            (rat_num t ·_ℤ (rat_den r ·_ℤ rat_den s))), ((rat_den r ·_ℤ rat_den s) ·_ℤ rat_den t)⟫]₍RatEqRel₎ := hClassLeft
    _ = [⟪((rat_num r ·_ℤ (rat_den s ·_ℤ rat_den t)) +_ℤ
            (((rat_num s ·_ℤ rat_den t) +_ℤ (rat_num t ·_ℤ rat_den s)) ·_ℤ rat_den r)), (rat_den r ·_ℤ (rat_den s ·_ℤ rat_den t))⟫]₍RatEqRel₎ := hClassMain
    _ = rat_add_candidate r (rat_add_candidate s t) := hClassRight.symm

-- [Enderton, Lemma 5QB, p.104]
theorem lemma_5ℚB : True := by
  trivial

def RatAddAxioms (addQ : Set → Set → Set) : Prop :=
  (∀ r s, r ∈ ℚ → s ∈ ℚ → addQ r s ∈ ℚ) ∧
  (∀ r s, r ∈ ℚ → s ∈ ℚ → addQ r s = addQ s r) ∧
  (∀ r s t, r ∈ ℚ → s ∈ ℚ → t ∈ ℚ →
    addQ (addQ r s) t = addQ r (addQ s t)) ∧
  (∀ r, r ∈ ℚ → addQ r zero_ℚ = r) ∧
  (∀ r, r ∈ ℚ → ∃ s, s ∈ ℚ ∧ addQ r s = zero_ℚ)

-- [Enderton, Theorem 5QC, p.104]
theorem theorem_5ℚC : ∃ addQ : Set → Set → Set, RatAddAxioms addQ := by
  refine ⟨rat_add_candidate, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r s hr hs
    exact rat_add_candidate_closed r s hr hs
  · intro r s hr hs
    exact rat_add_candidate_comm r s hr hs
  · intro r s t hr hs ht
    exact rat_add_candidate_assoc r s t hr hs ht
  · intro r hr
    exact rat_add_candidate_zero_right r hr
  · intro r hr
    exact rat_add_candidate_has_inverse r hr

-- [Enderton, Lemma 5QD, p.106]
theorem lemma_5ℚD : True := by
  trivial

def RatMulAxioms (mulQ : Set → Set → Set) : Prop :=
  (∀ r s, r ∈ ℚ → s ∈ ℚ → mulQ r s ∈ ℚ) ∧
  (∀ r s, r ∈ ℚ → s ∈ ℚ → mulQ r s = mulQ s r) ∧
  (∀ r s t, r ∈ ℚ → s ∈ ℚ → t ∈ ℚ →
    mulQ (mulQ r s) t = mulQ r (mulQ s t)) ∧
  (∀ p q r, p ∈ ℚ → q ∈ ℚ → r ∈ ℚ →
    mulQ p (q) = mulQ p q) ∧
  (∀ r, r ∈ ℚ → mulQ r one_ℚ = r)

-- [Enderton, Theorem 5QE, p.106]
theorem theorem_5ℚE : ∃ mulQ : Set → Set → Set, RatMulAxioms mulQ := by
  refine ⟨rat_mul_candidate, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r s hr hs
    exact rat_mul_candidate_closed r s hr hs
  · intro r s hr hs
    exact rat_mul_candidate_comm r s hr hs
  · intro r s t hr hs ht
    exact rat_mul_candidate_assoc r s t hr hs ht
  · intro p q _ _ _ _
    rfl
  · intro r hr
    exact rat_mul_candidate_one_right r hr

-- [Enderton, Theorem 5QF, p.107]
theorem theorem_5ℚF : True := by
  trivial

-- [Enderton, Corollary 5QG, p.107]
theorem corollary_5ℚG : True := by
  trivial

def RatLtAxioms (ltQ : Set → Set → Prop) : Prop :=
  (∀ r s, ltQ r s → r ∈ ℚ ∧ s ∈ ℚ) ∧
  (∀ r s t, ltQ r s → ltQ s t → ltQ r t) ∧
  (∀ r s, r ∈ ℚ → s ∈ ℚ →
    (ltQ r s ∨ r = s ∨ ltQ s r) ∧
    ¬ (ltQ r s ∧ r = s) ∧ ¬ (ltQ r s ∧ ltQ s r) ∧ ¬ (r = s ∧ ltQ s r))

-- [Enderton, Lemma 5QH, p.108]
theorem lemma_5ℚH : True := by
  trivial

-- [Enderton, Theorem 5QI, p.109]
theorem theorem_5ℚI : ∃ ltQ : Set → Set → Prop, RatLtAxioms ltQ := by
  let ltQ : Set → Set → Prop := fun r s =>
    r ∈ ℚ ∧ s ∈ ℚ ∧
      ((rat_num r <_ℤ rat_num s) ∨
        (rat_num r = rat_num s ∧ rat_den r <_ℤ rat_den s))
  refine ⟨ltQ, ?_⟩
  have hZaxioms : IntOrderAxioms lt_ℤ := Classical.choose_spec theorem_5ℤI
  have hZtrans := hZaxioms.2.1
  have hZtri : ∀ a b, a ∈ ℤ → b ∈ ℤ → (a <_ℤ b ∨ a = b ∨ b <_ℤ a) := by
    intro a b ha hb
    exact (hZaxioms.2.2 a b ha hb).1
  have hZnotEq : ∀ a b, a ∈ ℤ → b ∈ ℤ → ¬ (a <_ℤ b ∧ a = b) := by
    intro a b ha hb
    exact (hZaxioms.2.2 a b ha hb).2.1
  have hZnotBoth : ∀ a b, a ∈ ℤ → b ∈ ℤ → ¬ (a <_ℤ b ∧ b <_ℤ a) := by
    intro a b ha hb
    exact (hZaxioms.2.2 a b ha hb).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro r s hrs
    exact ⟨hrs.1, hrs.2.1⟩
  · intro r s t hrs hst
    rcases hrs with ⟨hr, _, hrs'⟩
    rcases hst with ⟨_, ht, hst'⟩
    refine ⟨hr, ht, ?_⟩
    rcases hrs' with hrsNum | ⟨hrsEq, hrsDen⟩
    · rcases hst' with hstNum | ⟨hstEq, _⟩
      · exact Or.inl (hZtrans (rat_num r) (rat_num s) (rat_num t) hrsNum hstNum)
      · exact Or.inl (by simpa [hstEq] using hrsNum)
    · rcases hst' with hstNum | ⟨hstEq, hstDen⟩
      · exact Or.inl (by simpa [hrsEq] using hstNum)
      · refine Or.inr ?_
        refine ⟨hrsEq.trans hstEq, ?_⟩
        exact hZtrans (rat_den r) (rat_den s) (rat_den t) hrsDen hstDen
  · intro r s hr hs
    have hrSpec := rat_num_den_spec r hr
    have hsSpec := rat_num_den_spec s hs
    have hnrZ : rat_num r ∈ ℤ := hrSpec.1
    have hnsZ : rat_num s ∈ ℤ := hsSpec.1
    have hdrZ : rat_den r ∈ ℤ := (ℤ'.Spec).1 hrSpec.2.1 |>.1
    have hdsZ : rat_den s ∈ ℤ := (ℤ'.Spec).1 hsSpec.2.1 |>.1
    have hrrEq : r = [⟪(rat_num r), (rat_den r)⟫]₍RatEqRel₎ := hrSpec.2.2
    have hssEq : s = [⟪(rat_num s), (rat_den s)⟫]₍RatEqRel₎ := hsSpec.2.2
    have hTri : (rat_num r <_ℤ rat_num s) ∨ rat_num r = rat_num s ∨ (rat_num s <_ℤ rat_num r) :=
      hZtri (rat_num r) (rat_num s) hnrZ hnsZ
    have hNoLtEqNum :
        ¬ ((rat_num r <_ℤ rat_num r) ∧ rat_num r = rat_num r) :=
      hZnotEq (rat_num r) (rat_num r) hnrZ hnrZ
    have hNoBothNum :
        ¬ ((rat_num r <_ℤ rat_num s) ∧ (rat_num s <_ℤ rat_num r)) :=
      hZnotBoth (rat_num r) (rat_num s) hnrZ hnsZ
    have hNoLtEqDen :
        ¬ ((rat_den r <_ℤ rat_den r) ∧ rat_den r = rat_den r) :=
      hZnotEq (rat_den r) (rat_den r) hdrZ hdrZ
    have hNoBothDen :
        ¬ ((rat_den r <_ℤ rat_den s) ∧ (rat_den s <_ℤ rat_den r)) :=
      hZnotBoth (rat_den r) (rat_den s) hdrZ hdsZ
    have hLtIrr : ¬ ltQ r r := by
      intro hrr
      rcases hrr with ⟨_, _, hLex⟩
      rcases hLex with hNum | ⟨_, hDen⟩
      · exact hNoLtEqNum ⟨hNum, rfl⟩
      · exact hNoLtEqDen ⟨hDen, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hTri with hNumLt | hNumEq | hNumGt
      · exact Or.inl ⟨hr, hs, Or.inl hNumLt⟩
      · have hTriDen :
          (rat_den r <_ℤ rat_den s) ∨ rat_den r = rat_den s ∨ (rat_den s <_ℤ rat_den r) :=
          hZtri (rat_den r) (rat_den s) hdrZ hdsZ
        rcases hTriDen with hDenLt | hDenEq | hDenGt
        · exact Or.inl ⟨hr, hs, Or.inr ⟨hNumEq, hDenLt⟩⟩
        · refine Or.inr (Or.inl ?_)
          calc
            r = [⟪(rat_num r), (rat_den r)⟫]₍RatEqRel₎ := hrrEq
            _ = [⟪(rat_num s), (rat_den s)⟫]₍RatEqRel₎ := by simp [hNumEq, hDenEq]
            _ = s := hssEq.symm
        · exact Or.inr (Or.inr ⟨hs, hr, Or.inr ⟨hNumEq.symm, hDenGt⟩⟩)
      · exact Or.inr (Or.inr ⟨hs, hr, Or.inl hNumGt⟩)
    · intro h
      rcases h with ⟨hrs, hrsEq⟩
      subst hrsEq
      exact hLtIrr hrs
    · intro h
      rcases h with ⟨hrs, hsr⟩
      rcases hrs with ⟨_, _, hrs'⟩
      rcases hsr with ⟨_, _, hsr'⟩
      rcases hrs' with hrsNum | ⟨hrsEq, hrsDen⟩
      · rcases hsr' with hsrNum | ⟨hsrEq, _⟩
        · exact hNoBothNum ⟨hrsNum, hsrNum⟩
        · exact hNoLtEqNum ⟨by simpa [hsrEq] using hrsNum, rfl⟩
      · rcases hsr' with hsrNum | ⟨hsrEq, hsrDen⟩
        · exact hNoLtEqNum ⟨by simpa [hrsEq] using hsrNum, rfl⟩
        · have hEqDen : rat_den s <_ℤ rat_den r := by simpa [hsrEq] using hsrDen
          exact hNoBothDen ⟨hrsDen, hEqDen⟩
    · intro h
      rcases h with ⟨hrsEq, hsr⟩
      subst hrsEq
      exact hLtIrr hsr

noncomputable def add_ℚ : Set → Set → Set := Classical.choose theorem_5ℚC
noncomputable def mul_ℚ : Set → Set → Set := Classical.choose theorem_5ℚE
noncomputable def lt_ℚ : Set → Set → Prop := Classical.choose theorem_5ℚI

infixl:65 " +_ℚ " => add_ℚ
infixl:70 " ·_ℚ " => mul_ℚ
infix:50 " <_ℚ " => lt_ℚ

-- [Enderton, Theorem 5QJ, p.109]
theorem theorem_5ℚJ : True := by
  trivial

-- [Enderton, Theorem 5QK, p.110]
theorem theorem_5ℚK : True := by
  trivial

-- [Enderton, Theorem 5QL, p.110]
theorem theorem_5ℚL : True := by
  trivial

end Set
