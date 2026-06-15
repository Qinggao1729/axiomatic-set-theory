import Set.Ch2

/-!
# Chapter 4, Section 1: Inductive Sets

Core natural-number construction in Enderton Ch4 §1 (Inductive Sets).

This file `#check`s the primitive Infinity axiom from `Set/Axioms.lean`,
derives Enderton's literal form `∃ A, Inductive A`, defines the carrier
`Infinity` as a `Classical.choose` witness (analogous to `Empty`,
`Pair`, … in Ch2 §1), and develops Theorems 4A–4C.
-/

namespace Set

/-- [Enderton Ch4 §1, p.68] "Definition: For any set `a`, its successor `a⁺` is
defined by `a⁺ = a ∪ {a}`." -/
noncomputable def Successor (a : Set) : Set := a ∪ {a}
postfix:90 "⁺" => Successor

/-- [Enderton Ch4 §1, p.68] "A set `A` is said to be inductive iff `∅ ∈ A` and it
is closed under successor, i.e., `(∀ a ∈ A) a⁺ ∈ A`." -/
def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A

-- [Enderton Ch4 §1, p.68] The primitive Infinity axiom is imported from
-- `Set/Axioms.lean` (in witness-expanded form); `#check` records its signature.
#check infinity

/-- [Enderton Ch4 §1, p.68] "Infinity Axiom: There exists an inductive set:
`(∃A)[∅ ∈ A ∧ (∀ a ∈ A) a⁺ ∈ A]`." Derived here from the primitive
(witness-expanded) Infinity axiom in `Set/Axioms.lean`. -/
theorem infinity_inductive : ∃ (A : Set), Inductive A := by
  rcases Set.infinity with ⟨A, hEmpty, hSucc⟩
  rcases hEmpty with ⟨e, heEmpty, heA⟩
  refine ⟨A, ?_⟩
  constructor
  · have heq : e = Set.Empty := by
      apply extensionality
      intro x
      constructor
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
      constructor
      · intro hx
        have hxa : x ∈ a ∨ x = a := (hsSpec x).1 hx
        simpa [Successor, Union.Spec, Singleton.Spec] using hxa
      · intro hx
        have hxa : x ∈ a ∨ x = a := by
          simpa [Successor, Union.Spec, Singleton.Spec] using hx
        exact (hsSpec x).2 hxa
    simpa [hsEq] using hsA

/-- A fixed inductive set chosen from `infinity_inductive`, analogous to `Empty`,
`Pair u v`, etc. in Ch2. (Implementation device, used as the carrier set `A` in the
textbook proof of Theorem 4A.) -/
noncomputable def Infinity : Set := Classical.choose infinity_inductive

lemma Infinity.Inductive : Inductive Infinity :=
  Classical.choose_spec infinity_inductive

/-- [Enderton Ch4 §1, p.68] "Definition: A natural number is a set that belongs to
every inductive set." -/
def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A

/-- [Enderton Ch4 §1, p.68] "Theorem 4A: There is a set whose members are exactly
the natural numbers."

Following the textbook proof: pick a fixed inductive set (here `Infinity`) and
carve out the elements that also belong to every *other* inductive set. -/
theorem thm_4A_natural_numbers_exist : ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n := by
  have hInfInd : Inductive Infinity := Infinity.Inductive
  obtain ⟨w, hw⟩ : ∃ (w : Set), ∀ (x : Set),
      x ∈ w ↔ x ∈ Infinity ∧ ∀ (A' : Set), A' ≠ Infinity ∧ Inductive A' → x ∈ A' :=
    comprehension _ Infinity
  refine ⟨w, ?_⟩
  intro n
  constructor
  · intro hnw
    obtain ⟨hnInf, hnOther⟩ := (hw n).mp hnw
    intro B hBind
    by_cases hBeq : B = Infinity
    · rw [hBeq]; exact hnInf
    · exact hnOther B ⟨hBeq, hBind⟩
  · intro hnat
    apply (hw n).mpr
    refine ⟨hnat Infinity hInfInd, ?_⟩
    intro B hB
    exact hnat B hB.2

/-- [Enderton Ch4 §1, p.69] "The set of all natural numbers is denoted by a
lowercase Greek omega: `x ∈ ω ⇔ x is a natural number ⇔ x belongs to every
inductive set`." -/
noncomputable def ω := Classical.choose thm_4A_natural_numbers_exist

-- The original wording is "In terms of classes, we have `ω = ⋂ {A | A is inductive}`,
-- but the class of all inductive sets is not a set."
-- The following lemma is the set-theoretic equivalent version of this.
-- We have not defined a proper class, but we might define one later (TODO).
@[simp]
lemma ω.Spec {n : Set} : n ∈ ω ↔ Natural n := by
  have h := Classical.choose_spec thm_4A_natural_numbers_exist
  rw [ω]
  simp_all



/-- [Enderton Ch4 §1, p.69] "Theorem 4B: `ω` is inductive, and is a subset of every
other inductive set." (First half: `ω` is inductive.)

Proof follows the textbook three-step chain `a ∈ ω → a belongs to every inductive
set → a⁺ belongs to every inductive set → a⁺ ∈ ω`. -/
theorem thm_4B_ω_inductive : Inductive ω := by
  refine ⟨?_, ?_⟩
  · rw [ω.Spec, Natural]
    intro A hA
    exact hA.left
  · intro n hn
    rw [ω.Spec, Natural]
    intro A hA
    apply hA.right n
    rw [ω.Spec, Natural] at hn
    exact hn A hA

/-- [Enderton Ch4 §1, p.69] "Theorem 4B: `ω` is inductive, and is a subset of every
other inductive set." (Second half: `ω` is the smallest inductive set; together
with `thm_4B_ω_inductive` this is the full content of Theorem 4B.) -/
theorem thm_4B_ω_subset_of_inductive : ∀ (A : Set), Inductive A → ω ⊆ A := by
  intro A hA n hn
  rw [ω.Spec, Natural] at hn
  exact hn A hA

/-- [Enderton Ch4 §1, p.69] "Induction Principle for `ω`: Any inductive subset of
`ω` coincides with `ω`."

Predicate form: given a base case `P ∅` and a successor step `P k → P (k⁺)` on `ω`,
the conclusion `P n` holds for all `n ∈ ω`. The proof builds `T = {n ∈ ω | P n}`,
shows it is inductive, hence `ω ⊆ T` by minimality, hence `P n` for every
`n ∈ ω`. -/
lemma ω_induction (P : Set → Prop)
    (hBase : P Set.Empty)
    (hStep : ∀ k, k ∈ ω → P k → P (k⁺)) :
    ∀ n, n ∈ ω → P n := by
  intro n hnω
  obtain ⟨T, hTspec⟩ : ∃ (T : Set), ∀ (k : Set), k ∈ T ↔ k ∈ ω ∧ P k :=
    comprehension _ ω
  have hTind : Inductive T := by
    refine ⟨?_, ?_⟩
    · exact (hTspec Set.Empty).2 ⟨thm_4B_ω_inductive.left, hBase⟩
    · intro k hk
      rcases (hTspec k).1 hk with ⟨hkω, hkP⟩
      exact (hTspec (k⁺)).2 ⟨thm_4B_ω_inductive.right k hkω, hStep k hkω hkP⟩
  have hωSubT : ω ⊆ T := thm_4B_ω_subset_of_inductive T hTind
  exact ((hTspec n).1 (hωSubT n hnω)).right

/-- [Enderton Ch4 §1, p.69] "Theorem 4C: Every natural number except 0 is the
successor of some natural number."

Textbook proof: apply the Induction Principle for `ω` to the predicate
`P n := n = ∅ ∨ ∃ p ∈ ω, n = p⁺`; the base case is the left disjunct, and the
inductive step uses the witness `p := k`. -/
theorem thm_4C_nonzero_natural_is_successor (n : Set) :
    n ≠ ∅ → Natural n → ∃ (m : Set), m ∈ ω ∧ n = m⁺ := by
  intro hne hnat
  have hnω : n ∈ ω := ω.Spec.mpr hnat
  have hP : ∀ k, k ∈ ω → (k = Set.Empty ∨ ∃ p, p ∈ ω ∧ k = p⁺) := by
    apply ω_induction (fun k => k = Set.Empty ∨ ∃ p, p ∈ ω ∧ k = p⁺)
    · left
      rfl
    · intro k hkω _
      right
      exact ⟨k, hkω, rfl⟩
  rcases hP n hnω with h | h
  · exact absurd h hne
  · exact h

end Set
