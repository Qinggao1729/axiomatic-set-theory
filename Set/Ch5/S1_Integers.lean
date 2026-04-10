import Set.Ch4.S5_OrderingOnOmega
import Set.Ch3.S6_Equivalence
import Set.Ch3.S4_Functions
import Set.Ch4.S4_Arithmetic

/-!
# Chapter 5, Section 1: Integers

Recovery rebuild of the Ch5 §1 file.
Tactics are placed before the integer theorem chain so later proofs can reuse
them directly.
-/

namespace Set

open Lean Elab Tactic
-- notation:90 "⟪" x ", " y "⟫" => OrderedPair x y

lemma nat_add_left_comm (a b c : Set) (ha : a ∈ ω) (hb : b ∈ ω) (hc : c ∈ ω) :
    a + (b + c) = b + (a + c) := by
  calc
    a + (b + c) = (a + b) + c := by
      rw [← nat_add_assoc a b c ha hb hc]
    _ = (b + a) + c := by
      rw [nat_add_comm a b ha hb]
    _ = b + (a + c) := by
      rw [nat_add_assoc b a c hb ha hc]

lemma nat_add_swap (a b c d : Set) (ha : a ∈ ω) (hb : b ∈ ω) (hc : c ∈ ω) (hd : d ∈ ω) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := by
      rw [nat_add_assoc a b (c + d) ha hb (nat_add_closed c d hc hd)]
    _ = a + (c + (b + d)) := by
      rw [nat_add_left_comm b c d hb hc hd]
    _ = (a + c) + (b + d) := by
      rw [← nat_add_assoc a c (b + d) ha hc (nat_add_closed b d hb hd)]

lemma nat_add_perm6
    (u v w x y z : Set)
    (hu : u ∈ ω) (hv : v ∈ ω) (hw : w ∈ ω) (hx : x ∈ ω) (hy : y ∈ ω) (hz : z ∈ ω) :
    (u + v) + (w + x + (y + z)) = (x + z) + (u + w + (y + v)) := by
  calc
    (u + v) + (w + x + (y + z))
        = (u + v) + ((w + x) + (y + z)) := by
            rw [nat_add_assoc w x (y + z) hw hx (nat_add_closed y z hy hz)]
    _ = ((u + v) + (w + x)) + (y + z) := by
            rw [← nat_add_assoc (u + v) (w + x) (y + z)
              (nat_add_closed u v hu hv) (nat_add_closed w x hw hx) (nat_add_closed y z hy hz)]
    _ = ((u + w) + (v + x)) + (y + z) := by
            rw [nat_add_swap u v w x hu hv hw hx]
    _ = (u + w) + ((v + x) + (y + z)) := by
            rw [nat_add_assoc (u + w) (v + x) (y + z)
              (nat_add_closed u w hu hw) (nat_add_closed v x hv hx) (nat_add_closed y z hy hz)]
    _ = (u + w) + ((v + y) + (x + z)) := by
            rw [nat_add_swap v x y z hv hx hy hz]
    _ = (u + w) + ((y + v) + (x + z)) := by
            rw [nat_add_comm v y hv hy]
    _ = (u + w) + ((x + z) + (y + v)) := by
            rw [nat_add_comm (y + v) (x + z) (nat_add_closed y v hy hv) (nat_add_closed x z hx hz)]
    _ = (x + z) + ((u + w) + (y + v)) := by
            rw [nat_add_left_comm (u + w) (x + z) (y + v)
              (nat_add_closed u w hu hw) (nat_add_closed x z hx hz) (nat_add_closed y v hy hv)]
    _ = (x + z) + (u + w + (y + v)) := by
            rfl

syntax "set_omega" : tactic
macro_rules
  | `(tactic| set_omega) => `(tactic|
      first
      | assumption
      | exact zero_ω_mem_ω
      | exact one_ω_mem_ω
      | exact nat_add_closed _ _ (by set_omega) (by set_omega)
      | exact nat_mul_closed _ _ (by set_omega) (by set_omega))

elab "set_perm" : tactic => do
  evalTactic (← `(tactic|
    first
    | (simp [*,
        nat_left_distrib, nat_right_distrib,
        nat_add_assoc, nat_add_comm, nat_add_left_comm, nat_add_swap,
        nat_mul_assoc, nat_mul_comm, nat_add_closed, nat_mul_closed] <;> try set_omega)
    | (simp [
        nat_left_distrib, nat_right_distrib,
        nat_add_assoc, nat_add_comm, nat_add_left_comm, nat_add_swap,
        nat_mul_assoc, nat_mul_comm, nat_add_closed, nat_mul_closed] <;> try set_omega)))

elab "set_commω" : tactic => do
  evalTactic (← `(tactic|
    first
    | exact nat_add_comm _ _ (by set_omega) (by set_omega)
    | rw [nat_add_comm _ _ (by set_omega) (by set_omega)]))

elab "set_swap4" : tactic => do
  evalTactic (← `(tactic|
    exact nat_add_swap _ _ _ _ (by set_omega) (by set_omega) (by set_omega) (by set_omega)))

elab "set_distribω" : tactic => do
  evalTactic (← `(tactic|
    first
    | rw [← nat_left_distrib _ _ _ (by set_omega) (by set_omega) (by set_omega)]
    | rw [← nat_right_distrib _ _ _ (by set_omega) (by set_omega) (by set_omega)]
    | rw [nat_left_distrib _ _ _ (by set_omega) (by set_omega) (by set_omega)]
    | rw [nat_right_distrib _ _ _ (by set_omega) (by set_omega) (by set_omega)]))

noncomputable def IntegerCarrier : Set := ω ⨯ ω

noncomputable def IntEqRel : Set :=
  Comprehension
    (fun w =>
      ∃ a b c d,
        a ∈ ω ∧ b ∈ ω ∧ c ∈ ω ∧ d ∈ ω ∧
        w = ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∧
        a + d = c + b)
    (IntegerCarrier ⨯ IntegerCarrier)

lemma IntEqRel.Spec {w : Set} :
    w ∈ IntEqRel ↔
      w ∈ (IntegerCarrier ⨯ IntegerCarrier) ∧
      ∃ a b c d,
        a ∈ ω ∧ b ∈ ω ∧ c ∈ ω ∧ d ∈ ω ∧
        w = ⟨⟨a, b⟩, ⟨c, d⟩⟩ ∧
        a + d = c + b := by
  simp [IntEqRel, Comprehension.Spec]

theorem theorem_5ℤA : IntEqRel.IsEquivalenceRelation IntegerCarrier := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w hw
    rcases (IntEqRel.Spec).1 hw with ⟨_, a, b, c, d, _, _, _, _, hEqPair, _⟩
    exact ⟨⟪a, b⟫, ⟪c, d⟫, hEqPair⟩
  · intro w hw
    exact (IntEqRel.Spec).1 hw |>.1
  · intro x hx
    rcases (Product.Spec (A := ω) (B := ω) (w := x)).1 (by simpa [IntegerCarrier] using hx) with
      ⟨a, b, ha, hb, rfl⟩
    rw [IntEqRel.Spec]
    refine ⟨?_, ?_⟩
    · exact Pair.mem_product IntegerCarrier IntegerCarrier
        (⟪a, b⟫) (⟪a, b⟫)
        (by simpa [IntegerCarrier] using Pair.mem_product ω ω a b ha hb)
        (by simpa [IntegerCarrier] using Pair.mem_product ω ω a b ha hb)
    · exact ⟨a, b, a, b, ha, hb, ha, hb, rfl, rfl⟩
  · intro x y hxy
    rcases (IntEqRel.Spec).1 hxy with
      ⟨hxyProd, a, b, c, d, ha, hb, hc, hd, hEqPair, hSum⟩
    have hx : x = ⟪a, b⟫ := (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hEqPair |>.1
    have hy : y = ⟪c, d⟫ := (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hEqPair |>.2
    have hxCarrier : x ∈ IntegerCarrier :=
      (Pair.mem_product_elim IntegerCarrier IntegerCarrier x y hxyProd).1
    have hyCarrier : y ∈ IntegerCarrier :=
      (Pair.mem_product_elim IntegerCarrier IntegerCarrier x y hxyProd).2
    rw [IntEqRel.Spec]
    refine ⟨?_, ?_⟩
    · exact Pair.mem_product IntegerCarrier IntegerCarrier y x hyCarrier hxCarrier
    · refine ⟨c, d, a, b, hc, hd, ha, hb, ?_, hSum.symm⟩
      simp [hx, hy]
  · intro x y z hxy hyz
    rcases (IntEqRel.Spec).1 hxy with
      ⟨hxyProd, a, b, c, d, ha, hb, hc, hd, hxyEq, hxySum⟩
    rcases (IntEqRel.Spec).1 hyz with
      ⟨hyzProd, c', d', e, f, hc', hd', he, hf, hyzEq, hyzSum⟩
    have hx : x = ⟪a, b⟫ := (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hxyEq |>.1
    have hy₁ : y = ⟪c, d⟫ := (OrderedPair.uniqueness x y (⟪a, b⟫) (⟪c, d⟫)).1 hxyEq |>.2
    have hy₂ : y = ⟪c', d'⟫ := (OrderedPair.uniqueness y z (⟪c', d'⟫) (⟪e, f⟫)).1 hyzEq |>.1
    have hz : z = ⟪e, f⟫ := (OrderedPair.uniqueness y z (⟪c', d'⟫) (⟪e, f⟫)).1 hyzEq |>.2
    have hcdEq : ⟪c, d⟫ = ⟪c', d'⟫ := hy₁.symm.trans hy₂
    have hcEq : c = c' := (OrderedPair.uniqueness c d c' d').1 hcdEq |>.1
    have hdEq : d = d' := (OrderedPair.uniqueness c d c' d').1 hcdEq |>.2
    subst c'
    subst d'
    have h₁ : a + (d + f) = c + (b + f) := by
      calc
        a + (d + f) = (a + d) + f := by rw [nat_add_assoc a d f ha hd hf]
        _ = (c + b) + f := by rw [hxySum]
        _ = c + (b + f) := by rw [← nat_add_assoc c b f hc hb hf]
    have h₂ : c + (f + b) = e + (d + b) := by
      calc
        c + (f + b) = (c + f) + b := by rw [nat_add_assoc c f b hc hf hb]
        _ = (e + d) + b := by rw [hyzSum]
        _ = e + (d + b) := by rw [← nat_add_assoc e d b he hd hb]
    have h₃ : a + (d + f) = e + (d + b) := by
      calc
        a + (d + f) = c + (b + f) := h₁
        _ = c + (f + b) := by rw [nat_add_comm b f hb hf]
        _ = e + (d + b) := h₂
    have h₄ : (a + f) + d = (e + b) + d := by
      calc
        (a + f) + d = a + (f + d) := by rw [nat_add_assoc a f d ha hf hd]
        _ = a + (d + f) := by rw [nat_add_comm f d hf hd]
        _ = e + (d + b) := h₃
        _ = e + (b + d) := by rw [nat_add_comm d b hd hb]
        _ = (e + b) + d := by rw [← nat_add_assoc e b d he hb hd]
    have hFinal : a + f = e + b := by
      exact nat_add_right_cancel (a + f) (e + b) d
        (nat_add_closed a f ha hf)
        (nat_add_closed e b he hb)
        hd
        h₄
    have hxCarrier : x ∈ IntegerCarrier :=
      (Pair.mem_product_elim IntegerCarrier IntegerCarrier x y hxyProd).1
    have hzCarrier : z ∈ IntegerCarrier :=
      (Pair.mem_product_elim IntegerCarrier IntegerCarrier y z hyzProd).2
    rw [IntEqRel.Spec]
    refine ⟨?_, ?_⟩
    · exact Pair.mem_product IntegerCarrier IntegerCarrier x z hxCarrier hzCarrier
    · refine ⟨a, b, e, f, ha, hb, he, hf, ?_, hFinal⟩
      simp [hx, hz]

noncomputable def IntegerSet : Set := IntegerCarrier / IntEqRel
notation "ℤ" => IntegerSet

noncomputable def zero_ℤ : Set := [⟪zero_ω, zero_ω⟫]₍IntEqRel₎
noncomputable def one_ℤ : Set := [⟪one_ω, zero_ω⟫]₍IntEqRel₎

def IntAddAxioms (addZ : Set → Set → Set) : Prop :=
  (∀ a b, a ∈ ℤ → b ∈ ℤ → addZ a b ∈ ℤ) ∧
  (∀ a b, a ∈ ℤ → b ∈ ℤ → addZ a b = addZ b a) ∧
  (∀ a b c, a ∈ ℤ → b ∈ ℤ → c ∈ ℤ →
    addZ (addZ a b) c = addZ a (addZ b c)) ∧
  (∀ a, a ∈ ℤ → addZ a zero_ℤ = a) ∧
  (∀ a, a ∈ ℤ → ∃ b, b ∈ ℤ ∧ addZ a b = zero_ℤ)

def IntMulAxioms (mulZ : Set → Set → Set) : Prop :=
  (∀ a b, a ∈ ℤ → b ∈ ℤ → mulZ a b ∈ ℤ) ∧
  (∀ a b, a ∈ ℤ → b ∈ ℤ → mulZ a b = mulZ b a) ∧
  (∀ a b c, a ∈ ℤ → b ∈ ℤ → c ∈ ℤ →
    mulZ (mulZ a b) c = mulZ a (mulZ b c)) ∧
  (∀ a, a ∈ ℤ → mulZ a one_ℤ = a) ∧
  zero_ℤ ≠ one_ℤ ∧
  (∀ a b, a ∈ ℤ → b ∈ ℤ → mulZ a b = zero_ℤ → a = zero_ℤ ∨ b = zero_ℤ)

def IntOrderAxioms (ltZ : Set → Set → Prop) : Prop :=
  (∀ a b, ltZ a b → a ∈ ℤ ∧ b ∈ ℤ) ∧
  (∀ a b c, ltZ a b → ltZ b c → ltZ a c) ∧
  (∀ a b, a ∈ ℤ → b ∈ ℤ →
    (ltZ a b ∨ a = b ∨ ltZ b a) ∧
    ¬ (ltZ a b ∧ a = b) ∧
    ¬ (ltZ a b ∧ ltZ b a) ∧
    ¬ (a = b ∧ ltZ b a))

lemma int_exists_rep (z : Set) (hz : z ∈ ℤ) :
    ∃ m n, m ∈ ω ∧ n ∈ ω ∧ z = [⟪m, n⟫]₍IntEqRel₎ := by
  rcases (QuotientSet.Spec).1 hz with ⟨_, x, hxCarrier, hzEq⟩
  rcases (Product.Spec (A := ω) (B := ω) (w := x)).1 (by simpa [IntegerCarrier] using hxCarrier) with
    ⟨m, n, hmω, hnω, hxEq⟩
  refine ⟨m, n, hmω, hnω, ?_⟩
  simpa [hxEq] using hzEq

noncomputable def int_rep_left (z : Set) (hz : z ∈ ℤ) : Set :=
  Classical.choose (int_exists_rep z hz)

noncomputable def int_rep_right (z : Set) (hz : z ∈ ℤ) : Set :=
  Classical.choose (Classical.choose_spec (int_exists_rep z hz))

lemma int_rep_spec (z : Set) (hz : z ∈ ℤ) :
    int_rep_left z hz ∈ ω ∧
    int_rep_right z hz ∈ ω ∧
    z = [⟪(int_rep_left z hz), (int_rep_right z hz)⟫]₍IntEqRel₎ := by
  exact Classical.choose_spec (Classical.choose_spec (int_exists_rep z hz))

lemma nat_order_right_cancel_mem
    (a b k : Set)
    (haω : a ∈ ω) (hbω : b ∈ ω) (hkω : k ∈ ω)
    (h : (a + k) ∈ (b + k)) :
    a ∈ b := by
  rcases natural_compare a b haω hbω with hab | habEq | hba
  · exact hab
  · exfalso
    have hsumω : a + k ∈ ω := nat_add_closed a k haω hkω
    have hNot : (a + k) ∉ (a + k) := natural_not_mem_self (a + k) hsumω
    exact hNot (by simpa [habEq] using h)
  · exfalso
    have hba' : (b + k) ∈ (a + k) :=
      nat_order_preserved_by_add b a k hbω haω hkω hba
    have hsumω : a + k ∈ ω := nat_add_closed a k haω hkω
    have hTrans : IsTransitiveSet (a + k) :=
      natural_transitive_set (a + k) ((ω.Spec).1 hsumω)
    have hSelf : (a + k) ∈ (a + k) := hTrans (a + k) (b + k) h hba'
    exact (natural_not_mem_self (a + k) hsumω) hSelf

lemma IntEqRel.pair_mem
    (a b c d : Set)
    (haω : a ∈ ω) (hbω : b ∈ ω) (hcω : c ∈ ω) (hdω : d ∈ ω)
    (hEq : a + d = c + b) :
    ⟨⟪a, b⟫, ⟪c, d⟫⟩ ∈ IntEqRel := by
  rw [IntEqRel.Spec]
  refine ⟨?_, ?_⟩
  · exact Pair.mem_product IntegerCarrier IntegerCarrier
      (⟪a, b⟫) (⟪c, d⟫)
      (by simpa [IntegerCarrier] using Pair.mem_product ω ω a b haω hbω)
      (by simpa [IntegerCarrier] using Pair.mem_product ω ω c d hcω hdω)
  · exact ⟨a, b, c, d, haω, hbω, hcω, hdω, rfl, hEq⟩

lemma zero_ℤ_mem_ℤ : zero_ℤ ∈ ℤ := by
  exact EquivalenceClass.mem_quotient IntegerCarrier IntEqRel
    (⟪zero_ω, zero_ω⟫)
    (by simpa [IntegerCarrier] using Pair.mem_product ω ω zero_ω zero_ω zero_ω_mem_ω zero_ω_mem_ω)

lemma one_ℤ_mem_ℤ : one_ℤ ∈ ℤ := by
  exact EquivalenceClass.mem_quotient IntegerCarrier IntEqRel
    (⟪one_ω, zero_ω⟫)
    (by simpa [IntegerCarrier] using Pair.mem_product ω ω one_ω zero_ω one_ω_mem_ω zero_ω_mem_ω)

noncomputable def int_add_candidate (a b : Set) : Set := by
  by_cases ha : a ∈ ℤ
  · by_cases hb : b ∈ ℤ
    · exact [⟪(int_rep_left a ha + int_rep_left b hb), (int_rep_right a ha + int_rep_right b hb)⟫]₍IntEqRel₎
    · exact zero_ℤ
  · exact zero_ℤ

noncomputable def int_mul_candidate (a b : Set) : Set := by
  by_cases ha : a ∈ ℤ
  · by_cases hb : b ∈ ℤ
    · exact [⟪((int_rep_left a ha * int_rep_left b hb) + (int_rep_right a ha * int_rep_right b hb)), ((int_rep_left a ha * int_rep_right b hb) + (int_rep_right a ha * int_rep_left b hb))⟫]₍IntEqRel₎
    · exact zero_ℤ
  · exact zero_ℤ

lemma int_add_candidate_spec
    (a b : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) :
    int_add_candidate a b =
      [⟪(int_rep_left a ha + int_rep_left b hb), (int_rep_right a ha + int_rep_right b hb)⟫]₍IntEqRel₎ := by
  simp [int_add_candidate, ha, hb]

lemma int_mul_candidate_spec
    (a b : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) :
    int_mul_candidate a b =
      [⟪((int_rep_left a ha * int_rep_left b hb) + (int_rep_right a ha * int_rep_right b hb)), ((int_rep_left a ha * int_rep_right b hb) + (int_rep_right a ha * int_rep_left b hb))⟫]₍IntEqRel₎ := by
  simp [int_mul_candidate, ha, hb]

lemma int_add_candidate_closed (a b : Set) :
    a ∈ ℤ → b ∈ ℤ → int_add_candidate a b ∈ ℤ := by
  intro ha hb
  rw [int_add_candidate_spec a b ha hb]
  have hlaω : int_rep_left a ha ∈ ω := (int_rep_spec a ha).1
  have hraω : int_rep_right a ha ∈ ω := (int_rep_spec a ha).2.1
  have hlbω : int_rep_left b hb ∈ ω := (int_rep_spec b hb).1
  have hrbω : int_rep_right b hb ∈ ω := (int_rep_spec b hb).2.1
  exact EquivalenceClass.mem_quotient IntegerCarrier IntEqRel
    (⟪(int_rep_left a ha + int_rep_left b hb), (int_rep_right a ha + int_rep_right b hb)⟫)
    (by
      simpa [IntegerCarrier] using Pair.mem_product ω ω
        (int_rep_left a ha + int_rep_left b hb)
        (int_rep_right a ha + int_rep_right b hb)
        (nat_add_closed _ _ hlaω hlbω)
        (nat_add_closed _ _ hraω hrbω))

lemma int_mul_candidate_closed (a b : Set) :
    a ∈ ℤ → b ∈ ℤ → int_mul_candidate a b ∈ ℤ := by
  intro ha hb
  rw [int_mul_candidate_spec a b ha hb]
  have hlaω : int_rep_left a ha ∈ ω := (int_rep_spec a ha).1
  have hraω : int_rep_right a ha ∈ ω := (int_rep_spec a ha).2.1
  have hlbω : int_rep_left b hb ∈ ω := (int_rep_spec b hb).1
  have hrbω : int_rep_right b hb ∈ ω := (int_rep_spec b hb).2.1
  exact EquivalenceClass.mem_quotient IntegerCarrier IntEqRel
    (⟪((int_rep_left a ha * int_rep_left b hb) + (int_rep_right a ha * int_rep_right b hb)), ((int_rep_left a ha * int_rep_right b hb) + (int_rep_right a ha * int_rep_left b hb))⟫)
    (by
      simpa [IntegerCarrier] using Pair.mem_product ω ω
        (((int_rep_left a ha * int_rep_left b hb) + (int_rep_right a ha * int_rep_right b hb)))
        (((int_rep_left a ha * int_rep_right b hb) + (int_rep_right a ha * int_rep_left b hb)))
        (by set_omega)
        (by set_omega))

lemma int_pair_add_congr
    (m n m' n' p q p' q' : Set)
    (hmω : m ∈ ω) (hnω : n ∈ ω) (hm'ω : m' ∈ ω) (hn'ω : n' ∈ ω)
    (hpω : p ∈ ω) (hqω : q ∈ ω) (hp'ω : p' ∈ ω) (hq'ω : q' ∈ ω)
    (hmn : m + n' = m' + n)
    (hpq : p + q' = p' + q) :
    ⟨⟪(m + p), (n + q)⟫, ⟪(m' + p'), (n' + q')⟫⟩ ∈ IntEqRel := by
  apply IntEqRel.pair_mem
  · exact nat_add_closed m p hmω hpω
  · exact nat_add_closed n q hnω hqω
  · exact nat_add_closed m' p' hm'ω hp'ω
  · exact nat_add_closed n' q' hn'ω hq'ω
  · calc
      (m + p) + (n' + q') = (m + n') + (p + q') := by
        rw [nat_add_swap m p n' q' hmω hpω hn'ω hq'ω]
      _ = (m' + n) + (p' + q) := by rw [hmn, hpq]
      _ = (m' + p') + (n + q) := by
        rw [nat_add_swap m' n p' q hm'ω hnω hp'ω hqω]

lemma int_add_candidate_comm (a b : Set) :
    a ∈ ℤ → b ∈ ℤ → int_add_candidate a b = int_add_candidate b a := by
  intro ha hb
  have hlaω : int_rep_left a ha ∈ ω := (int_rep_spec a ha).1
  have hraω : int_rep_right a ha ∈ ω := (int_rep_spec a ha).2.1
  have hlbω : int_rep_left b hb ∈ ω := (int_rep_spec b hb).1
  have hrbω : int_rep_right b hb ∈ ω := (int_rep_spec b hb).2.1
  let p1 : Set := ⟪(int_rep_left a ha + int_rep_left b hb), (int_rep_right a ha + int_rep_right b hb)⟫
  let p2 : Set := ⟪(int_rep_left b hb + int_rep_left a ha), (int_rep_right b hb + int_rep_right a ha)⟫
  have hp1 : p1 ∈ IntegerCarrier := by
    exact Pair.mem_product ω ω
      (int_rep_left a ha + int_rep_left b hb)
      (int_rep_right a ha + int_rep_right b hb)
      (nat_add_closed _ _ hlaω hlbω)
      (nat_add_closed _ _ hraω hrbω)
  have hp2 : p2 ∈ IntegerCarrier := by
    exact Pair.mem_product ω ω
      (int_rep_left b hb + int_rep_left a ha)
      (int_rep_right b hb + int_rep_right a ha)
      (nat_add_closed _ _ hlbω hlaω)
      (nat_add_closed _ _ hrbω hraω)
  have hRel : ⟨p1, p2⟩ ∈ IntEqRel := by
    apply IntEqRel.pair_mem
    · exact nat_add_closed _ _ hlaω hlbω
    · exact nat_add_closed _ _ hraω hrbω
    · exact nat_add_closed _ _ hlbω hlaω
    · exact nat_add_closed _ _ hrbω hraω
    · set_perm
  have hClass :
      [p1]₍IntEqRel₎ = [p2]₍IntEqRel₎ :=
    (equiv_class_eq_iff IntEqRel IntegerCarrier p1 p2 theorem_5ℤA hp1 hp2).2 hRel
  simpa [int_add_candidate_spec a b ha hb, int_add_candidate_spec b a hb ha, p1, p2] using hClass

lemma int_mul_candidate_comm (a b : Set) :
    a ∈ ℤ → b ∈ ℤ → int_mul_candidate a b = int_mul_candidate b a := by
  intro ha hb
  have hlaω : int_rep_left a ha ∈ ω := (int_rep_spec a ha).1
  have hraω : int_rep_right a ha ∈ ω := (int_rep_spec a ha).2.1
  have hlbω : int_rep_left b hb ∈ ω := (int_rep_spec b hb).1
  have hrbω : int_rep_right b hb ∈ ω := (int_rep_spec b hb).2.1
  let p1 : Set := ⟪((int_rep_left a ha * int_rep_left b hb) + (int_rep_right a ha * int_rep_right b hb)), ((int_rep_left a ha * int_rep_right b hb) + (int_rep_right a ha * int_rep_left b hb))⟫
  let p2 : Set := ⟪((int_rep_left b hb * int_rep_left a ha) + (int_rep_right b hb * int_rep_right a ha)), ((int_rep_left b hb * int_rep_right a ha) + (int_rep_right b hb * int_rep_left a ha))⟫
  have hp1 : p1 ∈ IntegerCarrier := by
    exact Pair.mem_product ω ω
      ((int_rep_left a ha * int_rep_left b hb) + (int_rep_right a ha * int_rep_right b hb))
      ((int_rep_left a ha * int_rep_right b hb) + (int_rep_right a ha * int_rep_left b hb))
      (by set_omega) (by set_omega)
  have hp2 : p2 ∈ IntegerCarrier := by
    exact Pair.mem_product ω ω
      ((int_rep_left b hb * int_rep_left a ha) + (int_rep_right b hb * int_rep_right a ha))
      ((int_rep_left b hb * int_rep_right a ha) + (int_rep_right b hb * int_rep_left a ha))
      (by set_omega) (by set_omega)
  have hRel : ⟨p1, p2⟩ ∈ IntEqRel := by
    apply IntEqRel.pair_mem
    · exact by set_omega
    · exact by set_omega
    · exact by set_omega
    · exact by set_omega
    · rw [
        nat_mul_comm (int_rep_left b hb) (int_rep_left a ha) (by set_omega) (by set_omega),
        nat_mul_comm (int_rep_right b hb) (int_rep_right a ha) (by set_omega) (by set_omega),
        nat_mul_comm (int_rep_left b hb) (int_rep_right a ha) (by set_omega) (by set_omega),
        nat_mul_comm (int_rep_right b hb) (int_rep_left a ha) (by set_omega) (by set_omega)
      ]
      rw [nat_add_comm
        (int_rep_right a ha * int_rep_left b hb)
        (int_rep_left a ha * int_rep_right b hb)
        (by set_omega) (by set_omega)]
  have hClass :
      [p1]₍IntEqRel₎ = [p2]₍IntEqRel₎ :=
    (equiv_class_eq_iff IntEqRel IntegerCarrier p1 p2 theorem_5ℤA hp1 hp2).2 hRel
  simpa [int_mul_candidate_spec a b ha hb, int_mul_candidate_spec b a hb ha, p1, p2] using hClass

lemma zero_ω_ne_one_ω : zero_ω ≠ one_ω := by
  intro hEq
  have hMemOne : zero_ω ∈ one_ω := by
    rw [one_ω]
    exact (mem_successor_iff zero_ω zero_ω).2 (Or.inr rfl)
  have hMemSelf : zero_ω ∈ zero_ω := by simpa [hEq] using hMemOne
  exact (natural_not_mem_self zero_ω zero_ω_mem_ω) hMemSelf

lemma zero_ℤ_ne_one_ℤ : zero_ℤ ≠ one_ℤ := by
  intro hEq
  let p0 : Set := ⟪zero_ω, zero_ω⟫
  let p1 : Set := ⟪one_ω, zero_ω⟫
  have hp0 : p0 ∈ IntegerCarrier := by
    simpa [p0, IntegerCarrier] using Pair.mem_product ω ω zero_ω zero_ω zero_ω_mem_ω zero_ω_mem_ω
  have hp1 : p1 ∈ IntegerCarrier := by
    simpa [p1, IntegerCarrier] using Pair.mem_product ω ω one_ω zero_ω one_ω_mem_ω zero_ω_mem_ω
  have hClass : [p0]₍IntEqRel₎ = [p1]₍IntEqRel₎ := by
    simpa [zero_ℤ, one_ℤ, p0, p1] using hEq
  have hRel : ⟨p0, p1⟩ ∈ IntEqRel :=
    (equiv_class_eq_iff IntEqRel IntegerCarrier p0 p1 theorem_5ℤA hp0 hp1).1 hClass
  rcases (IntEqRel.Spec).1 hRel with
    ⟨_, a, b, c, d, haω, hbω, hcω, hdω, hPairEq, hSum⟩
  have hAB : a = zero_ω ∧ b = zero_ω := by
    have hPair0 : p0 = ⟪a, b⟫ := (OrderedPair.uniqueness p0 p1 (⟪a, b⟫) (⟪c, d⟫)).1 hPairEq |>.1
    rcases (OrderedPair.uniqueness zero_ω zero_ω a b).1 (by simpa [p0] using hPair0) with ⟨ha0, hb0⟩
    exact ⟨ha0.symm, hb0.symm⟩
  have hCD : c = one_ω ∧ d = zero_ω := by
    have hPair1 : p1 = ⟪c, d⟫ := (OrderedPair.uniqueness p0 p1 (⟪a, b⟫) (⟪c, d⟫)).1 hPairEq |>.2
    rcases (OrderedPair.uniqueness one_ω zero_ω c d).1 (by simpa [p1] using hPair1) with ⟨hc1, hd0⟩
    exact ⟨hc1.symm, hd0.symm⟩
  rcases hAB with ⟨ha0, hb0⟩
  rcases hCD with ⟨hc1, hd0⟩
  subst a
  subst b
  subst c
  subst d
  have hZeroOne : zero_ω = one_ω := by
    calc
      zero_ω = zero_ω + zero_ω := by
        rw [nat_add_zero zero_ω zero_ω_mem_ω]
      _ = one_ω + zero_ω := by simpa using hSum
      _ = one_ω := by
        rw [nat_add_zero one_ω one_ω_mem_ω]
  exact zero_ω_ne_one_ω hZeroOne

lemma int_add_candidate_zero_right (a : Set) :
    a ∈ ℤ → int_add_candidate a zero_ℤ = a := by
  intro ha
  have hz : zero_ℤ ∈ ℤ := zero_ℤ_mem_ℤ
  have hlaω : int_rep_left a ha ∈ ω := (int_rep_spec a ha).1
  have hraω : int_rep_right a ha ∈ ω := (int_rep_spec a ha).2.1
  have hlzω : int_rep_left zero_ℤ hz ∈ ω := (int_rep_spec zero_ℤ hz).1
  have hrzω : int_rep_right zero_ℤ hz ∈ ω := (int_rep_spec zero_ℤ hz).2.1
  let pa : Set := ⟪(int_rep_left a ha), (int_rep_right a ha)⟫
  let pz : Set := ⟪(int_rep_left zero_ℤ hz), (int_rep_right zero_ℤ hz)⟫
  let p0 : Set := ⟪zero_ω, zero_ω⟫
  let ps : Set := ⟪(int_rep_left a ha + int_rep_left zero_ℤ hz), (int_rep_right a ha + int_rep_right zero_ℤ hz)⟫
  let pt : Set := ⟪(int_rep_left a ha + zero_ω), (int_rep_right a ha + zero_ω)⟫
  have hpzCarrier : pz ∈ IntegerCarrier := by
    simpa [pz, IntegerCarrier] using Pair.mem_product ω ω
      (int_rep_left zero_ℤ hz) (int_rep_right zero_ℤ hz) hlzω hrzω
  have hp0Carrier : p0 ∈ IntegerCarrier := by
    simpa [p0, IntegerCarrier] using Pair.mem_product ω ω
      zero_ω zero_ω zero_ω_mem_ω zero_ω_mem_ω
  have hpsCarrier : ps ∈ IntegerCarrier := by
    simpa [ps, IntegerCarrier] using Pair.mem_product ω ω
      (int_rep_left a ha + int_rep_left zero_ℤ hz)
      (int_rep_right a ha + int_rep_right zero_ℤ hz)
      (nat_add_closed _ _ hlaω hlzω)
      (nat_add_closed _ _ hraω hrzω)
  have hptCarrier : pt ∈ IntegerCarrier := by
    simpa [pt, IntegerCarrier] using Pair.mem_product ω ω
      (int_rep_left a ha + zero_ω)
      (int_rep_right a ha + zero_ω)
      (nat_add_closed _ _ hlaω zero_ω_mem_ω)
      (nat_add_closed _ _ hraω zero_ω_mem_ω)
  have hzRep : zero_ℤ = [pz]₍IntEqRel₎ := by
    simpa [pz] using (int_rep_spec zero_ℤ hz).2.2
  have hzClassEq : [pz]₍IntEqRel₎ = [p0]₍IntEqRel₎ := by
    calc
      [pz]₍IntEqRel₎ = zero_ℤ := hzRep.symm
      _ = [p0]₍IntEqRel₎ := by rfl
  have hpz0Rel : ⟨pz, p0⟩ ∈ IntEqRel :=
    (equiv_class_eq_iff IntEqRel IntegerCarrier pz p0 theorem_5ℤA hpzCarrier hp0Carrier).1 hzClassEq
  have hzEq : int_rep_left zero_ℤ hz + zero_ω = zero_ω + int_rep_right zero_ℤ hz := by
    rcases (IntEqRel.Spec).1 hpz0Rel with
      ⟨_, a1, b1, c1, d1, ha1ω, hb1ω, hc1ω, hd1ω, hPairEq, hSum⟩
    have hAB : a1 = int_rep_left zero_ℤ hz ∧ b1 = int_rep_right zero_ℤ hz := by
      have hPairL : pz = ⟪a1, b1⟫ :=
        (OrderedPair.uniqueness pz p0 (⟪a1, b1⟫) (⟪c1, d1⟫)).1 hPairEq |>.1
      rcases (OrderedPair.uniqueness (int_rep_left zero_ℤ hz) (int_rep_right zero_ℤ hz) a1 b1).1
          (by simpa [pz] using hPairL) with ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    have hCD : c1 = zero_ω ∧ d1 = zero_ω := by
      have hPairR : p0 = ⟪c1, d1⟫ :=
        (OrderedPair.uniqueness pz p0 (⟪a1, b1⟫) (⟪c1, d1⟫)).1 hPairEq |>.2
      rcases (OrderedPair.uniqueness zero_ω zero_ω c1 d1).1
          (by simpa [p0] using hPairR) with ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    rcases hAB with ⟨ha1, hb1⟩
    rcases hCD with ⟨hc1, hd1⟩
    subst a1
    subst b1
    subst c1
    subst d1
    simpa using hSum
  have hRelSum : ⟨ps, pt⟩ ∈ IntEqRel := by
    simpa [ps, pt, pa] using int_pair_add_congr
      (int_rep_left a ha) (int_rep_right a ha) (int_rep_left a ha) (int_rep_right a ha)
      (int_rep_left zero_ℤ hz) (int_rep_right zero_ℤ hz) zero_ω zero_ω
      hlaω hraω hlaω hraω hlzω hrzω zero_ω_mem_ω zero_ω_mem_ω
      rfl hzEq
  have hClassSP : [ps]₍IntEqRel₎ = [pt]₍IntEqRel₎ :=
    (equiv_class_eq_iff IntEqRel IntegerCarrier ps pt theorem_5ℤA hpsCarrier hptCarrier).2 hRelSum
  have hPtPa : [pt]₍IntEqRel₎ = [pa]₍IntEqRel₎ := by
    have hptEq : pt = pa := by
      simp [pt, pa, nat_add_zero, hlaω, hraω]
    simp [hptEq]
  have haRep : a = [pa]₍IntEqRel₎ := by
    simpa [pa] using (int_rep_spec a ha).2.2
  calc
    int_add_candidate a zero_ℤ = [ps]₍IntEqRel₎ := by
      simpa [ps] using int_add_candidate_spec a zero_ℤ ha hz
    _ = [pt]₍IntEqRel₎ := hClassSP
    _ = [pa]₍IntEqRel₎ := hPtPa
    _ = a := haRep.symm

lemma int_add_candidate_has_inverse (a : Set) :
    a ∈ ℤ → ∃ b, b ∈ ℤ ∧ int_add_candidate a b = zero_ℤ := by
  intro ha
  have hlaω : int_rep_left a ha ∈ ω := (int_rep_spec a ha).1
  have hraω : int_rep_right a ha ∈ ω := (int_rep_spec a ha).2.1
  let b : Set := [⟪(int_rep_right a ha), (int_rep_left a ha)⟫]₍IntEqRel₎
  have hb : b ∈ ℤ := by
    exact EquivalenceClass.mem_quotient IntegerCarrier IntEqRel
      (⟪(int_rep_right a ha), (int_rep_left a ha)⟫)
      (by
        simpa [IntegerCarrier] using Pair.mem_product ω ω
          (int_rep_right a ha) (int_rep_left a ha) hraω hlaω)
  have hlbω : int_rep_left b hb ∈ ω := (int_rep_spec b hb).1
  have hrbω : int_rep_right b hb ∈ ω := (int_rep_spec b hb).2.1
  let pb : Set := ⟪(int_rep_left b hb), (int_rep_right b hb)⟫
  let pSwap : Set := ⟪(int_rep_right a ha), (int_rep_left a ha)⟫
  let pSum : Set := ⟪(int_rep_left a ha + int_rep_left b hb), (int_rep_right a ha + int_rep_right b hb)⟫
  let p0 : Set := ⟪zero_ω, zero_ω⟫
  have hpbCarrier : pb ∈ IntegerCarrier := by
    simpa [pb, IntegerCarrier] using Pair.mem_product ω ω
      (int_rep_left b hb) (int_rep_right b hb) hlbω hrbω
  have hSwapCarrier : pSwap ∈ IntegerCarrier := by
    simpa [pSwap, IntegerCarrier] using Pair.mem_product ω ω
      (int_rep_right a ha) (int_rep_left a ha) hraω hlaω
  have hSumCarrier : pSum ∈ IntegerCarrier := by
    simpa [pSum, IntegerCarrier] using Pair.mem_product ω ω
      (int_rep_left a ha + int_rep_left b hb)
      (int_rep_right a ha + int_rep_right b hb)
      (nat_add_closed _ _ hlaω hlbω)
      (nat_add_closed _ _ hraω hrbω)
  have h0Carrier : p0 ∈ IntegerCarrier := by
    simpa [p0, IntegerCarrier] using Pair.mem_product ω ω zero_ω zero_ω zero_ω_mem_ω zero_ω_mem_ω
  have hbRep : b = [pb]₍IntEqRel₎ := by
    simpa [pb] using (int_rep_spec b hb).2.2
  have hbClass : [pb]₍IntEqRel₎ = [pSwap]₍IntEqRel₎ := by
    calc
      [pb]₍IntEqRel₎ = b := hbRep.symm
      _ = [pSwap]₍IntEqRel₎ := by rfl
  have hRelBS : ⟨pb, pSwap⟩ ∈ IntEqRel :=
    (equiv_class_eq_iff IntEqRel IntegerCarrier pb pSwap theorem_5ℤA hpbCarrier hSwapCarrier).1 hbClass
  have hBS :
      int_rep_left b hb + int_rep_left a ha =
      int_rep_right a ha + int_rep_right b hb := by
    rcases (IntEqRel.Spec).1 hRelBS with
      ⟨_, a1, b1, c1, d1, ha1ω, hb1ω, hc1ω, hd1ω, hPairEq, hSum⟩
    have hAB : a1 = int_rep_left b hb ∧ b1 = int_rep_right b hb := by
      have hL : pb = ⟪a1, b1⟫ :=
        (OrderedPair.uniqueness pb pSwap (⟪a1, b1⟫) (⟪c1, d1⟫)).1 hPairEq |>.1
      rcases (OrderedPair.uniqueness (int_rep_left b hb) (int_rep_right b hb) a1 b1).1
          (by simpa [pb] using hL) with ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    have hCD : c1 = int_rep_right a ha ∧ d1 = int_rep_left a ha := by
      have hR : pSwap = ⟪c1, d1⟫ :=
        (OrderedPair.uniqueness pb pSwap (⟪a1, b1⟫) (⟪c1, d1⟫)).1 hPairEq |>.2
      rcases (OrderedPair.uniqueness (int_rep_right a ha) (int_rep_left a ha) c1 d1).1
          (by simpa [pSwap] using hR) with ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    rcases hAB with ⟨ha1, hb1⟩
    rcases hCD with ⟨hc1, hd1⟩
    subst a1
    subst b1
    subst c1
    subst d1
    simpa using hSum
  have hASum :
      int_rep_left a ha + int_rep_left b hb =
      int_rep_right a ha + int_rep_right b hb := by
    calc
      int_rep_left a ha + int_rep_left b hb =
          int_rep_left b hb + int_rep_left a ha := by
            rw [nat_add_comm (int_rep_left a ha) (int_rep_left b hb) hlaω hlbω]
      _ = int_rep_right a ha + int_rep_right b hb := hBS
  have hRelSum0 : ⟨pSum, p0⟩ ∈ IntEqRel := by
    apply IntEqRel.pair_mem
    · exact nat_add_closed _ _ hlaω hlbω
    · exact nat_add_closed _ _ hraω hrbω
    · exact zero_ω_mem_ω
    · exact zero_ω_mem_ω
    · calc
        (int_rep_left a ha + int_rep_left b hb) + zero_ω =
            (int_rep_right a ha + int_rep_right b hb) + zero_ω := by
              rw [hASum]
        _ = (int_rep_right a ha + int_rep_right b hb) := by
              rw [nat_add_zero (int_rep_right a ha + int_rep_right b hb) (by set_omega)]
        _ = zero_ω + (int_rep_right a ha + int_rep_right b hb) := by
              have hxω : (int_rep_right a ha + int_rep_right b hb) ∈ ω := by set_omega
              exact (nat_zero_add (int_rep_right a ha + int_rep_right b hb) hxω).symm
  have hClassSum0 : [pSum]₍IntEqRel₎ = [p0]₍IntEqRel₎ :=
    (equiv_class_eq_iff IntEqRel IntegerCarrier pSum p0 theorem_5ℤA hSumCarrier h0Carrier).2 hRelSum0
  refine ⟨b, hb, ?_⟩
  calc
    int_add_candidate a b = [pSum]₍IntEqRel₎ := by
      simpa [pSum] using int_add_candidate_spec a b ha hb
    _ = [p0]₍IntEqRel₎ := hClassSum0
    _ = zero_ℤ := by rfl

lemma nat_mul_one_ω (m : Set) (hmω : m ∈ ω) : m * one_ω = m := by
  calc
    m * one_ω = m * zero_ω⁺ := by rw [one_ω]
    _ = (m * zero_ω) + m := nat_mul_succ m zero_ω hmω zero_ω_mem_ω
    _ = zero_ω + m := by rw [nat_mul_zero m hmω]
    _ = m := nat_zero_add m hmω

theorem theorem_5ℤF :
    ∃ addZ mulZ,
      IntAddAxioms addZ ∧
      IntMulAxioms mulZ ∧
      ∀ a b c, a ∈ ℤ → b ∈ ℤ → c ∈ ℤ →
        mulZ a (addZ b c) = addZ (mulZ a b) (mulZ a c) := by
  refine ⟨int_add_candidate, int_mul_candidate, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact int_add_candidate_closed
    · exact int_add_candidate_comm
    · sorry
    · exact int_add_candidate_zero_right
    · exact int_add_candidate_has_inverse
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact int_mul_candidate_closed
    · exact int_mul_candidate_comm
    · sorry
    · sorry
    · exact zero_ℤ_ne_one_ℤ
    · sorry
  · sorry

theorem theorem_5ℤC : ∃ addZ : Set → Set → Set, IntAddAxioms addZ := by
  rcases theorem_5ℤF with ⟨addZ, _, hAdd, _, _⟩
  exact ⟨addZ, hAdd⟩

theorem theorem_5ℤD (addZ : Set → Set → Set) (hAddAxioms : IntAddAxioms addZ) :
    (∀ a, a ∈ ℤ → addZ a zero_ℤ = a) ∧
    (∀ a, a ∈ ℤ → ∃ b, b ∈ ℤ ∧ addZ a b = zero_ℤ) := by
  exact ⟨hAddAxioms.2.2.2.1, hAddAxioms.2.2.2.2⟩

theorem theorem_5ℤE : ∃ mulZ : Set → Set → Set, IntMulAxioms mulZ := by
  rcases theorem_5ℤF with ⟨_, mulZ, _, hMul, _⟩
  exact ⟨mulZ, hMul⟩

theorem theorem_5ℤG (mulZ : Set → Set → Set) (hMulAxioms : IntMulAxioms mulZ) :
    (∀ a, a ∈ ℤ → mulZ a one_ℤ = a) ∧
    zero_ℤ ≠ one_ℤ ∧
    (∀ a b, a ∈ ℤ → b ∈ ℤ → mulZ a b = zero_ℤ → a = zero_ℤ ∨ b = zero_ℤ) := by
  exact ⟨hMulAxioms.2.2.2.1, hMulAxioms.2.2.2.2.1, hMulAxioms.2.2.2.2.2⟩

theorem theorem_5ℤI : ∃ ltZ : Set → Set → Prop, IntOrderAxioms ltZ := by
  letI : DecidablePred (fun x : Set => x ∈ ℤ) := Classical.decPred (fun x : Set => x ∈ ℤ)
  let ltZ : Set → Set → Prop := fun a b =>
    if ha : a ∈ ℤ then
      if hb : b ∈ ℤ then
        (int_rep_left a ha + int_rep_right b hb) ∈ (int_rep_left b hb + int_rep_right a ha)
      else False
    else False
  refine ⟨ltZ, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a ∈ ℤ
    · by_cases hb : b ∈ ℤ
      · exact ⟨ha, hb⟩
      · simp [ltZ, ha, hb] at hab
    · simp [ltZ, ha] at hab
  · intro a b c hab hbc
    have ha : a ∈ ℤ := by
      by_cases h : a ∈ ℤ
      · exact h
      · simp [ltZ, h] at hab
    have hb : b ∈ ℤ := by
      by_cases h : b ∈ ℤ
      · exact h
      · simp [ltZ, ha, h] at hab
    have hc : c ∈ ℤ := by
      by_cases h : c ∈ ℤ
      · exact h
      · simp [ltZ, hb, h] at hbc
    have hab' :
        (int_rep_left a ha + int_rep_right b hb) ∈
          (int_rep_left b hb + int_rep_right a ha) := by
      simpa [ltZ, ha, hb] using hab
    have hbc' :
        (int_rep_left b hb + int_rep_right c hc) ∈
          (int_rep_left c hc + int_rep_right b hb) := by
      simpa [ltZ, hb, hc] using hbc
    have h1ω := (int_rep_spec a ha).1
    have h2ω := (int_rep_spec a ha).2.1
    have h3ω := (int_rep_spec b hb).1
    have h4ω := (int_rep_spec b hb).2.1
    have h5ω := (int_rep_spec c hc).1
    have h6ω := (int_rep_spec c hc).2.1
    have hAdd₁ :
        ((int_rep_left a ha + int_rep_right b hb) + int_rep_right c hc) ∈
        ((int_rep_left b hb + int_rep_right a ha) + int_rep_right c hc) :=
      nat_order_preserved_by_add
        (int_rep_left a ha + int_rep_right b hb)
        (int_rep_left b hb + int_rep_right a ha)
        (int_rep_right c hc)
        (by set_omega) (by set_omega) (by set_omega)
        hab'
    have hAdd₂ :
        ((int_rep_left b hb + int_rep_right c hc) + int_rep_right a ha) ∈
        ((int_rep_left c hc + int_rep_right b hb) + int_rep_right a ha) :=
      nat_order_preserved_by_add
        (int_rep_left b hb + int_rep_right c hc)
        (int_rep_left c hc + int_rep_right b hb)
        (int_rep_right a ha)
        (by set_omega) (by set_omega) (by set_omega)
        hbc'
    have h₁ :
        ((int_rep_left a ha + int_rep_right c hc) + int_rep_right b hb) ∈
        ((int_rep_left b hb + int_rep_right c hc) + int_rep_right a ha) := by
      calc
        ((int_rep_left a ha + int_rep_right c hc) + int_rep_right b hb)
            = ((int_rep_left a ha + int_rep_right b hb) + int_rep_right c hc) := by
                rw [nat_add_assoc (int_rep_left a ha) (int_rep_right c hc) (int_rep_right b hb)
                  (by set_omega) (by set_omega) (by set_omega)]
                rw [nat_add_comm (int_rep_right c hc) (int_rep_right b hb) (by set_omega) (by set_omega)]
                rw [← nat_add_assoc (int_rep_left a ha) (int_rep_right b hb) (int_rep_right c hc)
                  (by set_omega) (by set_omega) (by set_omega)]
        _ ∈ ((int_rep_left b hb + int_rep_right a ha) + int_rep_right c hc) := hAdd₁
        _ = ((int_rep_left b hb + int_rep_right c hc) + int_rep_right a ha) := by
              calc
                ((int_rep_left b hb + int_rep_right a ha) + int_rep_right c hc)
                    = int_rep_left b hb + (int_rep_right a ha + int_rep_right c hc) := by
                        rw [nat_add_assoc (int_rep_left b hb) (int_rep_right a ha) (int_rep_right c hc)
                          (by set_omega) (by set_omega) (by set_omega)]
                _ = int_rep_left b hb + (int_rep_right c hc + int_rep_right a ha) := by
                        rw [nat_add_comm (int_rep_right a ha) (int_rep_right c hc) (by set_omega) (by set_omega)]
                _ = ((int_rep_left b hb + int_rep_right c hc) + int_rep_right a ha) := by
                        rw [← nat_add_assoc (int_rep_left b hb) (int_rep_right c hc) (int_rep_right a ha)
                          (by set_omega) (by set_omega) (by set_omega)]
    have h₂ :
        ((int_rep_left b hb + int_rep_right c hc) + int_rep_right a ha) ∈
        ((int_rep_left c hc + int_rep_right a ha) + int_rep_right b hb) := by
      calc
        ((int_rep_left b hb + int_rep_right c hc) + int_rep_right a ha) ∈
          ((int_rep_left c hc + int_rep_right b hb) + int_rep_right a ha) := hAdd₂
        _ = ((int_rep_left c hc + int_rep_right a ha) + int_rep_right b hb) := by
              rw [nat_add_assoc (int_rep_left c hc) (int_rep_right b hb) (int_rep_right a ha)
                (by set_omega) (by set_omega) (by set_omega)]
              rw [nat_add_comm (int_rep_right b hb) (int_rep_right a ha) (by set_omega) (by set_omega)]
              rw [← nat_add_assoc (int_rep_left c hc) (int_rep_right a ha) (int_rep_right b hb)
                (by set_omega) (by set_omega) (by set_omega)]
    have hTransSet :
        IsTransitiveSet ((int_rep_left c hc + int_rep_right a ha) + int_rep_right b hb) :=
      natural_transitive_set
        ((int_rep_left c hc + int_rep_right a ha) + int_rep_right b hb)
        ((ω.Spec).1 (by set_omega))
    have h₃ :
        ((int_rep_left a ha + int_rep_right c hc) + int_rep_right b hb) ∈
        ((int_rep_left c hc + int_rep_right a ha) + int_rep_right b hb) :=
      hTransSet _ _ h₁ h₂
    have hFinal :
        (int_rep_left a ha + int_rep_right c hc) ∈
        (int_rep_left c hc + int_rep_right a ha) :=
      nat_order_right_cancel_mem
        (int_rep_left a ha + int_rep_right c hc)
        (int_rep_left c hc + int_rep_right a ha)
        (int_rep_right b hb)
        (by set_omega) (by set_omega) (by set_omega) h₃
    simpa [ltZ, ha, hc] using hFinal
  · intro a b ha hb
    have h1ω := (int_rep_spec a ha).1
    have h2ω := (int_rep_spec a ha).2.1
    have h3ω := (int_rep_spec b hb).1
    have h4ω := (int_rep_spec b hb).2.1
    have hCmp := natural_trichotomy
      (int_rep_left a ha + int_rep_right b hb)
      (int_rep_left b hb + int_rep_right a ha)
      (by set_omega) (by set_omega)
    rcases hCmp with ⟨hTri, _, _, _⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hTri with hab | habEq | hba
      · exact Or.inl (by simpa [ltZ, ha, hb] using hab)
      · right
        left
        let pa : Set := ⟪(int_rep_left a ha), (int_rep_right a ha)⟫
        let pb : Set := ⟪(int_rep_left b hb), (int_rep_right b hb)⟫
        have hpaω : pa ∈ IntegerCarrier := by
          exact Pair.mem_product ω ω _ _ h1ω h2ω
        have hpbω : pb ∈ IntegerCarrier := by
          exact Pair.mem_product ω ω _ _ h3ω h4ω
        have hRel : ⟨pa, pb⟩ ∈ IntEqRel := by
          rw [IntEqRel.Spec]
          refine ⟨?_, ?_⟩
          · exact Pair.mem_product IntegerCarrier IntegerCarrier pa pb hpaω hpbω
          · refine ⟨int_rep_left a ha, int_rep_right a ha, int_rep_left b hb, int_rep_right b hb,
              h1ω, h2ω, h3ω, h4ω, rfl, habEq⟩
        have hClass :
            [pa]₍IntEqRel₎ = [pb]₍IntEqRel₎ :=
          (equiv_class_eq_iff IntEqRel IntegerCarrier pa pb theorem_5ℤA hpaω hpbω).2 hRel
        have haRep := (int_rep_spec a ha).2.2
        have hbRep := (int_rep_spec b hb).2.2
        calc
          a = [pa]₍IntEqRel₎ := by simpa [pa] using haRep
          _ = [pb]₍IntEqRel₎ := hClass
          _ = b := by simpa [pb] using hbRep.symm
      · exact Or.inr (Or.inr (by simpa [ltZ, hb, ha] using hba))
    · intro h
      rcases h with ⟨hab, habEq⟩
      have hab' :
          (int_rep_left a ha + int_rep_right b hb) ∈
            (int_rep_left b hb + int_rep_right a ha) := by
        simpa [ltZ, ha, hb] using hab
      have hSelf :
          (int_rep_left a ha + int_rep_right a ha) ∈
            (int_rep_left a ha + int_rep_right a ha) := by
        simpa [habEq] using hab'
      exact (natural_not_mem_self (int_rep_left a ha + int_rep_right a ha) (by set_omega)) hSelf
    · intro h
      rcases h with ⟨hab, hba⟩
      have hab' :
          (int_rep_left a ha + int_rep_right b hb) ∈
            (int_rep_left b hb + int_rep_right a ha) := by
        simpa [ltZ, ha, hb] using hab
      have hba' :
          (int_rep_left b hb + int_rep_right a ha) ∈
            (int_rep_left a ha + int_rep_right b hb) := by
        simpa [ltZ, hb, ha] using hba
      have hsumω : (int_rep_left a ha + int_rep_right b hb) ∈ ω := by set_omega
      have hTrans : IsTransitiveSet (int_rep_left a ha + int_rep_right b hb) :=
        natural_transitive_set _ ((ω.Spec).1 hsumω)
      have hSelf : (int_rep_left a ha + int_rep_right b hb) ∈ (int_rep_left a ha + int_rep_right b hb) :=
        hTrans _ _ hab' hba'
      exact (natural_not_mem_self _ hsumω) hSelf
    · intro h
      rcases h with ⟨habEq, hba⟩
      have hba' :
          (int_rep_left b hb + int_rep_right a ha) ∈
            (int_rep_left a ha + int_rep_right b hb) := by
        simpa [ltZ, hb, ha] using hba
      have hSelf :
          (int_rep_left a ha + int_rep_right a ha) ∈
            (int_rep_left a ha + int_rep_right a ha) := by
        simpa [habEq] using hba'
      exact (natural_not_mem_self (int_rep_left a ha + int_rep_right a ha) (by set_omega)) hSelf

noncomputable def add_ℤ : Set → Set → Set := Classical.choose theorem_5ℤF
noncomputable def mul_ℤ : Set → Set → Set := Classical.choose (Classical.choose_spec theorem_5ℤF)
noncomputable def lt_ℤ : Set → Set → Prop := Classical.choose theorem_5ℤI

infixl:65 " +_ℤ " => add_ℤ
infixl:70 " ·_ℤ " => mul_ℤ
infix:50 " <_ℤ " => lt_ℤ

lemma add_ℤ_axioms : IntAddAxioms add_ℤ := by
  exact (Classical.choose_spec (Classical.choose_spec theorem_5ℤF)).1

lemma mul_ℤ_axioms : IntMulAxioms mul_ℤ := by
  exact (Classical.choose_spec (Classical.choose_spec theorem_5ℤF)).2.1

lemma mul_ℤ_left_distrib (a b c : Set) (ha : a ∈ ℤ) (hb : b ∈ ℤ) (hc : c ∈ ℤ) :
    a ·_ℤ (b +_ℤ c) = (a ·_ℤ b) +_ℤ (a ·_ℤ c) := by
  exact (Classical.choose_spec (Classical.choose_spec theorem_5ℤF)).2.2 a b c ha hb hc

lemma lt_ℤ_axioms : IntOrderAxioms lt_ℤ := by
  exact Classical.choose_spec theorem_5ℤI

lemma int_pair_mul_congr
    (a b c d a' b' c' d' : Set)
    (haω : a ∈ ω) (hbω : b ∈ ω) (hcω : c ∈ ω) (hdω : d ∈ ω)
    (ha'ω : a' ∈ ω) (hb'ω : b' ∈ ω) (hc'ω : c' ∈ ω) (hd'ω : d' ∈ ω)
    (hab : a + b' = a' + b)
    (hcd : c + d' = c' + d) :
    ((a * c) + (b * d)) + ((a' * d') + (b' * c')) =
      ((a' * c') + (b' * d')) + ((a * d) + (b * c)) := by
  -- Textbook Lemma 5ZE method:
  -- build four equations from (1) and (2), then add them and cancel extras.
  have A1 : (a * c) + (b' * c) = (a' * c) + (b * c) := by
    have h := congrArg (fun t => t * c) hab
    calc
      (a * c) + (b' * c) = (a + b') * c := by
        set_distribω
      _ = (a' + b) * c := h
      _ = (a' * c) + (b * c) := by
        set_distribω
  have A2 : (a' * d) + (b * d) = (a * d) + (b' * d) := by
    have h := congrArg (fun t => t * d) hab
    calc
      (a' * d) + (b * d) = (a' + b) * d := by
        set_distribω
      _ = (a + b') * d := h.symm
      _ = (a * d) + (b' * d) := by
        set_distribω
  have A3 : (a' * c) + (a' * d') = (a' * c') + (a' * d) := by
    have h := congrArg (fun t => a' * t) hcd
    calc
      (a' * c) + (a' * d') = a' * (c + d') := by
        set_distribω
      _ = a' * (c' + d) := h
      _ = (a' * c') + (a' * d) := by
        set_distribω
  have A4 : (b' * c') + (b' * d) = (b' * c) + (b' * d') := by
    have h := congrArg (fun t => b' * t) hcd
    calc
      (b' * c') + (b' * d) = b' * (c' + d) := by
        set_distribω
      _ = b' * (c + d') := h.symm
      _ = (b' * c) + (b' * d') := by
        set_distribω
  have hsumEq :
      ((((a * c) + (b' * c)) + ((a' * d) + (b * d))) +
          (((a' * c) + (a' * d')) + ((b' * c') + (b' * d)))) =
      ((((a' * c) + (b * c)) + ((a * d) + (b' * d))) +
          (((a' * c') + (a' * d)) + ((b' * c) + (b' * d'))) ) := by
    rw [A1, A2, A3, A4]
  let K : Set := ((a' * c) + (a' * d)) + ((b' * c) + (b' * d))
  have hLeft :
      (((a * c) + (b * d)) + ((a' * d') + (b' * c'))) + K =
      ((((a * c) + (b' * c)) + ((a' * d) + (b * d))) +
        (((a' * c) + (a' * d')) + ((b' * c') + (b' * d)))) := by
    simp [K]
    rw [nat_add_swap
      ((a * c) + (b * d)) ((a' * d') + (b' * c')) ((a' * c) + (a' * d)) ((b' * c) + (b' * d))
      (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
    rw [nat_add_swap
      (a * c) (b * d) (a' * c) (a' * d)
      (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
    rw [nat_add_comm (b * d) (a' * d) (by set_omega) (by set_omega)]
    rw [nat_add_swap
      (a' * d') (b' * c') (b' * c) (b' * d)
      (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
    rw [nat_add_comm (a' * d') (b' * c) (by set_omega) (by set_omega)]
    rw [nat_add_swap
      ((a * c) + (a' * c)) ((a' * d) + (b * d)) ((b' * c) + (a' * d')) ((b' * c') + (b' * d))
      (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
    rw [nat_add_swap
      (a * c) (a' * c) (b' * c) (a' * d')
      (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
    rw [nat_add_swap
      ((a * c) + (b' * c)) ((a' * c) + (a' * d')) ((a' * d) + (b * d)) ((b' * c') + (b' * d))
      (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
  have hRight :
      ((((a' * c) + (b * c)) + ((a * d) + (b' * d))) +
        (((a' * c') + (a' * d)) + ((b' * c) + (b' * d')))) =
      (((a' * c') + (b' * d')) + ((a * d) + (b * c))) + K := by
    have hInner :
        (a' * c + b' * d) + (a' * d + a' * c' + (b' * c + b' * d')) =
        (a' * c' + b' * d') + (a' * c + a' * d + (b' * c + b' * d)) := by
      simpa using nat_add_perm6
        (a' * c) (b' * d) (a' * d) (a' * c') (b' * c) (b' * d')
        (by set_omega) (by set_omega) (by set_omega)
        (by set_omega) (by set_omega) (by set_omega)
    calc
      ((((a' * c) + (b * c)) + ((a * d) + (b' * d))) + (((a' * c') + (a' * d)) + ((b' * c) + (b' * d'))))
          = ((a' * c + b * c) + (a * d + b' * d)) + (a' * c' + a' * d + (b' * c + b' * d')) := by
              rw [nat_add_assoc (a' * c + b * c) (a * d + b' * d) (a' * c' + a' * d + (b' * c + b' * d'))
                (by set_omega) (by set_omega) (by set_omega)]
      _ = ((a' * c + a * d) + (b * c + b' * d)) + (a' * c' + a' * d + (b' * c + b' * d')) := by
              rw [nat_add_swap (a' * c) (b * c) (a * d) (b' * d)
                (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
      _ = ((a * d + a' * c) + (b * c + b' * d)) + (a' * c' + a' * d + (b' * c + b' * d')) := by
              rw [nat_add_comm (a' * c) (a * d) (by set_omega) (by set_omega)]
      _ = ((a * d + b * c) + (a' * c + b' * d)) + (a' * c' + a' * d + (b' * c + b' * d')) := by
              rw [nat_add_swap (a * d) (a' * c) (b * c) (b' * d)
                (by set_omega) (by set_omega) (by set_omega) (by set_omega)]
      _ = (a * d + b * c) + ((a' * c + b' * d) + (a' * c' + a' * d + (b' * c + b' * d'))) := by
              rw [nat_add_assoc (a * d + b * c) (a' * c + b' * d) (a' * c' + a' * d + (b' * c + b' * d'))
                (by set_omega) (by set_omega) (by set_omega)]
      _ = (a * d + b * c) + ((a' * c + b' * d) + (a' * d + a' * c' + (b' * c + b' * d'))) := by
              rw [nat_add_comm (a' * c') (a' * d) (by set_omega) (by set_omega)]
      _ = (a * d + b * c) + ((a' * c' + b' * d') + (a' * c + a' * d + (b' * c + b' * d))) := by
              rw [hInner]
      _ = ((a * d + b * c) + (a' * c' + b' * d')) + (a' * c + a' * d + (b' * c + b' * d)) := by
              rw [← nat_add_assoc (a * d + b * c) (a' * c' + b' * d') (a' * c + a' * d + (b' * c + b' * d))
                (by set_omega) (by set_omega) (by set_omega)]
      _ = ((a' * c' + b' * d') + (a * d + b * c)) + (a' * c + a' * d + (b' * c + b' * d)) := by
              rw [nat_add_comm (a * d + b * c) (a' * c' + b' * d') (by set_omega) (by set_omega)]
      _ = a' * c' + b' * d' + (a * d + b * c) + (a' * c + a' * d + (b' * c + b' * d)) := by
              rw [nat_add_assoc (a' * c' + b' * d') (a * d + b * c) (a' * c + a' * d + (b' * c + b' * d))
                (by set_omega) (by set_omega) (by set_omega)]
      _ = (((a' * c') + (b' * d')) + ((a * d) + (b * c))) + K := by
              simp [K]
  have hMain :
      (((a * c) + (b * d)) + ((a' * d') + (b' * c'))) + K =
      (((a' * c') + (b' * d')) + ((a * d) + (b * c))) + K := by
    exact hLeft.trans (hsumEq.trans hRight)
  exact nat_add_right_cancel
    (((a * c) + (b * d)) + ((a' * d') + (b' * c')))
    (((a' * c') + (b' * d')) + ((a * d) + (b * c)))
    K
    (by set_omega)
    (by set_omega)
    (by set_omega)
    hMain

end Set
