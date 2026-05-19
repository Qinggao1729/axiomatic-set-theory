import Set.Ch3.S2_Relations

/-!
# Choice Axiom Declarations

Canonical home for the Axiom of Choice and its equivalent forms.

## Why this file exists

Following the "axioms live in their own file, `#check`'d from the section
file in which they are introduced" convention used elsewhere in the
project (see also `Set/Axioms.lean`). This is especially important for AC:
because of its non-constructive nature, we want a single place that
collects all forms together, distinct from the ordinary theorem files.

## Why this file only imports `Set.Ch3.S2_Relations`

We want `Set/Ch3/S4_Functions.lean` to be able to `import Set.Choice` so
that Enderton's Theorem 3J(b) (the first textbook application of AC) can
be stated and proved *inside* `S4_Functions.lean`. To avoid a circular
import, the AC declarations cannot mention `IsFunction` (which is defined
in `S4_Functions.lean`). We therefore state each form with the function
predicate inlined — the inlined conjunction `IsRelation H ∧ ∀ x ∈ dom H,
∃! y, ⟪x, y⟫ ∈ H` is *definitionally* equal to `IsFunction H`, so callers
in `S4_Functions.lean` and downstream can destructure it as `IsFunction`
without any conversion lemma.

## Roadmap (six equivalent forms)

`ChoiceFirstForm` and `ChoiceSecondForm` below are the only ones Enderton
introduces in Chapter 3 (§Functions and §Infinite Cartesian Products,
respectively). The remaining four equivalent forms (Chapter 6) and their
inter-equivalences will be added here so all six live side-by-side.

Each form is wrapped in the `Set.Choice` sub-namespace; every consumer
must `open Choice` (or fully qualify) to access them, which makes every
AC dependency visible at the use site.
-/

namespace Set
namespace Choice

/--
[Enderton Ch3 §Functions, p. 49] **Axiom of Choice (first form).**
For any relation `R` there is a function `H ⊆ R` with `dom H = dom R`.

The "function" conjunct is inlined as `IsRelation H ∧ ∀ x ∈ dom H, ∃! y,
⟪x, y⟫ ∈ H` to keep this file independent of `Set/Ch3/S4_Functions.lean`;
the inlined form is definitionally equal to `IsFunction H`, so callers in
`S4_Functions.lean` use it as such.
-/
def ChoiceFirstForm : Prop :=
  ∀ (R : Set), IsRelation R →
    ∃ (H : Set), H ⊆ R ∧
      (IsRelation H ∧ ∀ x, x ∈ (dom H) → ∃! y, ⟪x, y⟫ ∈ H) ∧
      (dom H) = (dom R)

/-- The first-form Axiom of Choice itself. -/
axiom choice_first_form : ChoiceFirstForm

/--
[Enderton Ch3 §Infinite Cartesian Products, p. 55] **Axiom of Choice
(second / selector-function form).** For any indexed family `H` whose
fibers are nonempty, there is a selector function on `I`.

The "function" conjunct on `f` is inlined for the same reason as above.
-/
def ChoiceSecondForm : Prop :=
  ∀ (I H : Set),
    (IsRelation H ∧ ∀ x, x ∈ (dom H) → ∃! y, ⟪x, y⟫ ∈ H) →
    (dom H) = I →
    (∀ i, i ∈ I → ∃ hi, ⟪i, hi⟫ ∈ H ∧ hi.Nonempty) →
    ∃ f,
      (IsRelation f ∧ ∀ x, x ∈ (dom f) → ∃! y, ⟪x, y⟫ ∈ f) ∧
      (dom f) = I ∧
      ∀ i y, ⟪i, y⟫ ∈ f → ∃ hi, ⟪i, hi⟫ ∈ H ∧ y ∈ hi

-- TODO: The remaining four equivalent forms (Chapter 6) and their pairwise
-- equivalence theorems will be added below as the formalization
-- progresses.

end Choice
end Set
