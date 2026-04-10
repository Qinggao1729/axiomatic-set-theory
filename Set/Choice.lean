import Set.Ch3.S4_Functions

/-!
# Choice Axiom Declarations

Canonical declarations for AC live in this file.
`Set/Ch3/S5_InfiniteCartesianProducts.lean` imports this file, uses `#check`
for cross-reference, and develops AC-dependent theorems.
-/

namespace Set

-- [Enderton Ch3 §Functions, p.49] Axiom of Choice (first form).
def ChoiceFirstForm : Prop :=
  ∀ (R : Set), IsRelation R → ∃ (H : Set), H ⊆ R ∧ IsFunction H ∧ (dom H) = (dom R)

-- [Enderton Ch3 §Functions, p.49] First-form AC assumption.
axiom choice_first_form : ChoiceFirstForm

-- [Enderton Ch3 §Infinite Cartesian Products, p.55] Selector-function form.
def ChoiceSecondForm : Prop :=
  ∀ (I H : Set),
    IsFunction H →
    (dom H) = I →
    (∀ i, i ∈ I → ∃ hi, ⟨i, hi⟩ ∈ H ∧ hi.Nonempty) →
    ∃ f, IsFunction f ∧ (dom f) = I ∧
      ∀ i y, ⟨i, y⟩ ∈ f → ∃ hi, ⟨i, hi⟩ ∈ H ∧ y ∈ hi

end Set

