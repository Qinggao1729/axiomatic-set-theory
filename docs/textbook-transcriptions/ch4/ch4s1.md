# Ch4 Section 1 (Inductive Sets) - Textbook Extraction Draft

Source: Enderton, Chapter 4 "Inductive Sets", pp. 67-70 in `135 Elements of Set Theory - Enderton.pdf`.

## Core definitions and claims (book order)

1. Successor of a set (p.68)
   - Set theory: `a⁺ = a ∪ {a}`.
   - Lean map: `noncomputable def Successor (a : Set) : Set := a ∪ Singleton a`.

2. Inductive set (p.68)
   - Set theory: `Inductive(A) ↔ (0 ∈ A ∧ (∀ a ∈ A, a⁺ ∈ A))`.
   - Lean map: `def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A`.

3. Infinity axiom (p.68)
   - Textbook form: existence of an inductive set.
   - In this repo, primitive `infinity` is stronger/expanded and then specialized by:
   - Lean map: `theorem infinity_inductive : ∃ (A : Set), Inductive A`.

4. Natural number (p.68)
   - Set theory: `Natural(n) ↔ n belongs to every inductive set`.
   - Lean map: `def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A`.

5. Theorem 4A (p.68): existence of `ω`
   - Set theory: `∃ ω, ∀ n, n ∈ ω ↔ Natural(n)`.
   - Lean map:
     - `theorem natural_numbers_exist : ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n`
     - `noncomputable def ω := Classical.choose natural_numbers_exist`
     - `lemma ω.Spec {n : Set} : n ∈ ω ↔ Natural n`.

6. Theorem 4B (p.69): minimality/inductiveness of `ω`
   - Set theory:
     - `Inductive(ω)`
     - `∀ A, Inductive(A) → ω ⊆ A`.
   - Lean map:
     - `theorem ω.inductive : Inductive ω`
     - `theorem ω.subset_of_inductive : ∀ (A : Set), Inductive A → ω ⊆ A`.

7. Induction principle for `ω` (p.69)
   - Narrative form: any inductive subset of `ω` equals `ω`.
   - Predicate form used in Lean:
     - `(P(0) ∧ (∀ k ∈ ω, P(k) → P(k⁺))) → ∀ n ∈ ω, P(n)`.
   - Lean map:
     - `lemma ω_induction (P : Set → Prop) ... : ∀ n, n ∈ ω → P n`.

8. Theorem 4C (p.69): every nonzero natural has a predecessor
   - Set theory: `n ≠ 0 ∧ Natural(n) → ∃ m ∈ ω, n = m⁺`.
   - Lean map:
     - `theorem ω.exists_successor (n : Set) : n ≠ ∅ → Natural n → ∃ (m : Set), m ∈ ω ∧ n = m⁺`.

## Proof-flow notes from the textbook

- 4A uses one fixed inductive set `A` (from Infinity), then a subset/comprehension carve-out to define the set of objects that belong to every inductive set.
- 4B is immediate from the definition `x ∈ ω ↔ x belongs to every inductive set`.
- Induction principle is exactly minimality of `ω`: if `T ⊆ ω` is inductive, then `ω ⊆ T`; together with `T ⊆ ω`, conclude `T = ω`.
- 4C defines `T = { n ∈ ω | n = 0 or ∃ p ∈ ω, n = p⁺ }`, proves `T` inductive, then applies induction.

