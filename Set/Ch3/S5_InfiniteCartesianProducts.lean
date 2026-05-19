import Set.Ch3.S4_Functions

/-!
# Chapter 3, Section 5: Infinite Cartesian Products

Infinite Cartesian products and the AC-dependent nonempty-product theorem.

Theorem 3J (left/right inverse characterisations) and the first-form Axiom
of Choice both live in `Set/Ch3/S4_Functions.lean` inside the `Choice`
namespace. We re-`open Choice` here to mirror the AC-dependence marker.

`Set.Choice` is the *only* namespace where the AC declarations are in
scope; this file declares its dependence by opening it once at the top.
-/

namespace Set

open Choice

#check ChoiceFirstForm
#check choice_first_form
#check ChoiceSecondForm

-- Infinite Cartesian product Π_{i∈I} H(i), represented via relation-valued H.
noncomputable def InfiniteProduct (I H : Set) : Set :=
  Comprehension
    (fun f =>
      IsFunction f ∧ (dom f) = I ∧
      ∀ i y, i ∈ I → ⟪i, y⟫ ∈ f → ∃ hi, ⟪i, hi⟫ ∈ H ∧ y ∈ hi)
    (𝒫 (I ⨯ ⋃ (ran H)))

lemma InfiniteProduct.Spec {I H f : Set} :
    f ∈ InfiniteProduct I H ↔
      f ∈ 𝒫 (I ⨯ ⋃ (ran H)) ∧
      IsFunction f ∧ (dom f) = I ∧
      (∀ i y, i ∈ I → ⟪i, y⟫ ∈ f → ∃ hi, ⟪i, hi⟫ ∈ H ∧ y ∈ hi) := by
  simp [InfiniteProduct, Comprehension.Spec]

-- Enderton p.55: second-form AC yields nonempty infinite products.
theorem infiniteProduct_nonempty_of_choice_second_form
  (hChoice₂ : ChoiceSecondForm) :
  ∀ (I H : Set),
    IsFunction H →
    (dom H) = I →
    (∀ i, i ∈ I → ∃ hi, ⟪i, hi⟫ ∈ H ∧ hi.Nonempty) →
    (InfiniteProduct I H).Nonempty := by
  intro I H hHfun hDomH hFibers
  rcases hChoice₂ I H hHfun hDomH hFibers with ⟨f, hFfun, hDomF, hSel⟩
  have hPow : f ∈ 𝒫 (I ⨯ ⋃ (ran H)) := by
    rw [Power.Spec]
    intro w hwf
    rcases hFfun.1 w hwf with ⟨i, y, hEqw⟩
    have hiyf : ⟪i, y⟫ ∈ f := by simpa [hEqw] using hwf
    have hiDom : i ∈ dom f := Relation.Pair.mem_dom f i y hiyf
    have hiI : i ∈ I := by simpa [hDomF] using hiDom
    rcases hSel i y hiyf with ⟨hi, hihH, hyhi⟩
    have hhiRan : hi ∈ ran H := Relation.Pair.mem_ran H i hi hihH
    have hyBigUnion : y ∈ ⋃ (ran H) := (BigUnion.Spec).2 ⟨hi, hhiRan, hyhi⟩
    have hiyProd : ⟪i, y⟫ ∈ I ⨯ ⋃ (ran H) :=
      (Product.Pair.Spec).2 ⟨hiI, hyBigUnion⟩
    simpa [hEqw] using hiyProd
  have hfProd : f ∈ InfiniteProduct I H := (InfiniteProduct.Spec).2
    ⟨hPow, hFfun, hDomF, by
      intro i y hiI hiyf
      exact hSel i y hiyf⟩
  exact ⟨f, hfProd⟩

end Set
