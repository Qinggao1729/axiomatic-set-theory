import Set.Ch3.S4_Functions

/-!
# Chapter 3, Section 5: Infinite Cartesian Products

Infinite Cartesian products and the AC-dependent nonempty-product theorem.

Theorem 3J (left/right inverse characterizations) and first-form AC live in
`Set/Ch3/S4_Functions.lean` (inside `Set.Choice`).
-/

namespace Set

/--
[Enderton Ch3 §5, p.54] "Let `I` be a set ... and let `H` be a function whose
domain includes `I` ... We define
`⨉_{i ∈ I} H(i) = { f | f is a function with domain I and (∀ i ∈ I), f(i) ∈ H(i) }`."

Design choice:
- We keep the textbook clause in app-style (`f⟮i⟯ ∈ H⟮i⟯`) so the Lean surface
  reads like the text.
- The existential witnesses
  `∃ (hFfun : IsFunction f), ∃ (hDomF : (dom f) = I), ...`
  are exactly the two textbook side clauses ("`f` is a function" and
  "`dom f = I`"), now made explicit as local hypotheses so `f⟮i⟯` elaborates.

Caveat (why not the simple conjunction with automatic `f(i)`):
if we write
`IsFunction f ∧ (dom f) = I ∧ ∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯`,
then at the point where `f⟮i⟯` is elaborated, `IsFunction f` and `(dom f) = I`
are only sibling conjuncts, not local hypotheses, so automation cannot synthesize
the side conditions for `f⟮i⟯`.
-/
noncomputable def InfiniteProduct (I H : Set) (hH : IsFunction H) (hIH : I ⊆ dom H) : Set :=
  Comprehension
    (fun f =>
      ∃ (hFfun : IsFunction f), ∃ (hDomF : (dom f) = I),
        ∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯)
    (𝒫 (I ⨯ ⋃ (ran H)))

-- Uncommenting this direct conjunction attempt fails at `f⟮i⟯` elaboration
-- for the reason explained above (the side conditions are not in local context).

-- noncomputable def InfiniteProduct_conj_attempt
--     (I H : Set) (hH : IsFunction H) (hIH : I ⊆ dom H) : Set :=
--   Comprehension
--     (fun f =>
--       IsFunction f ∧ (dom f) = I ∧
--       (∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯))
--     (𝒫 (I ⨯ ⋃ (ran H)))


@[simp]
lemma InfiniteProduct.Spec_full {I H f : Set} (hH : IsFunction H) (hIH : I ⊆ dom H) :
    f ∈ InfiniteProduct I H hH hIH ↔
      f ∈ 𝒫 (I ⨯ ⋃ (ran H)) ∧
      ∃ (hFfun : IsFunction f), ∃ (hDomF : (dom f) = I),
        ∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯ := by
  simp [InfiniteProduct, Comprehension.Spec]


@[simp]
lemma InfiniteProduct.Spec {I H f : Set} (hH : IsFunction H) (hIH : I ⊆ dom H) :
    f ∈ InfiniteProduct I H hH hIH ↔
      ∃ (hFfun : IsFunction f), ∃ (hDomF : (dom f) = I),
        ∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯ := by
  constructor
  · intro hf
    exact ((InfiniteProduct.Spec_full hH hIH).1 hf).2
  · intro hf
    rcases hf with ⟨hFfun, hDomF, hSel⟩
    have hPow : f ∈ 𝒫 (I ⨯ ⋃ (ran H)) := by
      rw [Power.Spec]
      intro w hwf
      rcases hFfun.1 w hwf with ⟨i, y, hEqw⟩
      subst hEqw
      have hiDom : i ∈ dom f := Relation.Pair.mem_dom f i y hwf
      have hiI : i ∈ I := by simpa [hDomF] using hiDom
      refine (Product.Pair.Spec).2 ⟨?_, ?_⟩
      · exact hiI
      · have hfi_eq : f⟮i⟯ = y := FunctionValue.eq_of_pair' f i y ⟨hFfun, hiDom⟩ hwf
        subst y
        have hfi_mem : f⟮i⟯ ∈ H⟮i⟯ := hSel i hiI
        have hHiRan : H⟮i⟯ ∈ ran H := FunctionValue.mem_ran H i hH (hIH i hiI)
        exact (BigUnion.Spec).2 ⟨H⟮i⟯, hHiRan, hfi_mem⟩
    exact (InfiniteProduct.Spec_full hH hIH).2 ⟨hPow, hFfun, hDomF, hSel⟩
attribute [set_spec_simps] InfiniteProduct.Spec

/-- [Enderton Ch3 §5, p.55] "If any one `H(i)` is empty, then clearly the product
`⨉_{i ∈ I} H(i)` is empty." -/
theorem infiniteProduct_empty_of_empty_fiber
  (I H i : Set)
  (hHfun : IsFunction H)
  (hIH : I ⊆ dom H)
  (hiI : i ∈ I)
  (hHiEmpty : H⟮i⟯ = Set.Empty) :
  InfiniteProduct I H hHfun hIH = Set.Empty := by
  apply empty_eq_empty
  intro f hfProd
  rcases (InfiniteProduct.Spec hHfun hIH).1 hfProd with ⟨_, _, hSel⟩
  have hyHi : f⟮i⟯ ∈ H⟮i⟯ := hSel i hiI
  rw [hHiEmpty] at hyHi
  exact (Empty.Spec hyHi)

/-- [Enderton Ch6 §5, p.151] "Multiplicative axiom. The Cartesian product of nonempty sets is always nonempty.
That is, if `H` is a function with domain `I` and if `(∀i ∈ I) H(i) ≠ ∅`, then there is a function
`f` with domain `I` such that `(∀i ∈ I) f(i) ∈ H(i)`." -/
def ChoiceSecondForm : Prop :=
  ∀ (I H : Set) (hHfun : IsFunction H) (hDomH : (dom H) = I)
    (hFibers : ∀ i (hiI : i ∈ I), (H⟮i⟯).Nonempty),
    ∃ (f : Set), ∃ (hFfun : IsFunction f), ∃ (hDomF : (dom f) = I),
      (∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯)

/- AC declarations and AC-dependent theorems are placed in `Set.Choice`. -/
namespace Choice

/-- [Enderton Ch6 §5, p.151] Second-form Axiom of Choice. -/
axiom choice_second_form : ChoiceSecondForm

end Choice

/-- [Enderton Ch3 §5, p.55] Axiom of Choice (second form) here in terms of infinite product:
"For any set `I` and any function `H` with domain `I`,
if `H(i) ≠ ∅` for all `i` in `I`, then `⨉_{i ∈ I} H(i) ≠ ∅`. -/
def InfiniteProductNonemptyForm : Prop :=
  ∀ (I H : Set) (hHfun : IsFunction H) (hDomH : (dom H) = I)
    (hFibers : ∀ i (hiI : i ∈ I), (H⟮i⟯).Nonempty),
    (InfiniteProduct I H hHfun (by simp [hDomH])).Nonempty

/-- Here we show that the second-form Axiom of Choice in §6 is equivalent to the infinite product form here.
Not shown in the textbook. Does not require AC.-/
theorem choice_second_form_iff_infiniteProduct_nonempty :
    ChoiceSecondForm ↔ InfiniteProductNonemptyForm := by
  constructor
  · intro hChoice
    intro I H hHfun hDomH hFibers
    have hIH : I ⊆ dom H := by simp [hDomH]
    rcases hChoice I H hHfun hDomH hFibers with ⟨f, hFfun, hDomF, hSelApp⟩
    have hfProd : f ∈ InfiniteProduct I H hHfun hIH := (InfiniteProduct.Spec hHfun hIH).2
      ⟨hFfun, hDomF, hSelApp⟩
    exact ⟨f, hfProd⟩
  · intro hNonempty
    intro I H hHfun hDomH hFibers
    have hIH : I ⊆ dom H := by simp [hDomH]
    rcases hNonempty I H hHfun hDomH hFibers with ⟨f, hfProd⟩
    rcases (InfiniteProduct.Spec hHfun hIH).1 hfProd with ⟨hFfun, hDomF, hSelApp⟩
    exact ⟨f, hFfun, hDomF, hSelApp⟩


namespace Choice

/-- Here we are declaring the infinite product form of the second-form Axiom of Choice as a theorem
**only** in `Choice` namespace.-/
theorem infiniteProduct_nonempty_of_nonempty_fibers
    (I H : Set) (hHfun : IsFunction H) (hDomH : (dom H) = I)
    (hFibers : ∀ i (hiI : i ∈ I), (H⟮i⟯).Nonempty) :
    (InfiniteProduct I H hHfun (by simp [hDomH])).Nonempty := by
  exact (Set.choice_second_form_iff_infiniteProduct_nonempty).1
    choice_second_form I H hHfun hDomH hFibers

/-- The combination of some empty fiber → empty product (no AC) and no empty fibers → nonempty product (AC).
Basically the combination of the previous two theorems.
The verbosity comes from showing `∀ i (hiI : i ∈ I), (H⟮i⟯).Nonempty`from `¬∃ i hiI, H⟮i⟯'(⋯) = ∅`.
This is because we define `Nonempty A` as `∃ x, x ∈ A`, not `A ≠ ∅`. -/
theorem infiniteProduct_empty_iff_empty_fiber
    (I H : Set) (hHfun : IsFunction H) (hDomH : (dom H) = I) :
    InfiniteProduct I H hHfun (by simp [hDomH]) = Set.Empty ↔
      ∃ i, ∃ hiI : i ∈ I, H⟮i⟯ = Set.Empty := by
  constructor
  · intro hProdEmpty
    by_contra hNoEmptyFiber
    have hFibers : ∀ i (hiI : i ∈ I), (H⟮i⟯).Nonempty := by
      intro i hiI
      by_contra hNotNonempty
      refine hNoEmptyFiber ⟨i, hiI, ?_⟩
      exact (not_nonempty_iff_eq_empty H⟮i⟯).1 hNotNonempty
    rcases infiniteProduct_nonempty_of_nonempty_fibers I H hHfun hDomH hFibers with ⟨f, hfProd⟩
    rw [hProdEmpty] at hfProd
    exact Empty.Spec hfProd
  · rintro ⟨i, hiI, hHiEmpty⟩
    exact infiniteProduct_empty_of_empty_fiber I H i hHfun (by simp [hDomH]) hiI hHiEmpty

end Choice
end Set
