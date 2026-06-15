import Set.Ch2.S2_ArbitraryUnionsIntersections
import Set.Ch3.S2_Relations

/-!
# Choice Axiom Declarations

Canonical home for shared AC infrastructure and selected AC forms.

## Why this file exists

Following the "axioms live in their own file, `#check`'d from the section
file in which they are introduced" convention used elsewhere in the
project (see also `Set/Axioms.lean`). This is especially important for AC:
because of its non-constructive nature, we want a single place that
collects all forms together, distinct from the ordinary theorem files.

## Why function predicates are inlined

This file intentionally avoids importing `Set/Ch3/S4_Functions.lean`, so
it keeps a local function predicate:
`IsRelation F ∧ ∀ x ∈ dom F, ∃! y, ⟪x, y⟫ ∈ F`.

## Roadmap (six equivalent forms)

Enderton Theorem 6M (p.151) lists six equivalent forms. We keep forms
that are not being introduced locally in chapter files. Currently this file
contains forms III/IV/VI directly. Form I is defined in
`Set/Ch3/S4_Functions.lean`, form II is defined in
`Set/Ch3/S5_InfiniteCartesianProducts.lean`, and form V (cardinal
comparability) is intentionally deferred until the cardinal-comparison
layer is formalized.

Each form is wrapped in the `Set.Choice` sub-namespace; every consumer
must `open Choice` (or fully qualify) to access them, which makes every
AC dependency visible at the use site.
-/

namespace Set
namespace Choice

/-- Inlined "function on relations" predicate used in Choice forms. -/
def IsFunction' (F : Set) : Prop :=
  IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟪x, y⟫ ∈ F

/--
[Enderton Ch6 §Axiom of Choice, Theorem 6M(3), p.151]
For any set `A`, there is a choice function on the nonempty subsets of `A`.
-/
def ChoiceThirdForm : Prop :=
  ∀ (A : Set),
    ∃ (F : Set),
      IsFunction' F ∧
      (∀ B, B ∈ (dom F) ↔ B ⊆ A ∧ B.Nonempty) ∧
      (∀ B x, ⟪B, x⟫ ∈ F → x ∈ B)

/--
[Enderton Ch6 §Axiom of Choice, Theorem 6M(4), p.151]
If `𝒜` is a set of pairwise disjoint nonempty sets, there is a set `C`
containing exactly one element from each member of `𝒜`.
-/
def ChoiceFourthForm : Prop :=
  ∀ (𝒜 : Set),
    (∀ B, B ∈ 𝒜 → B.Nonempty) →
    (∀ B B', B ∈ 𝒜 → B' ∈ 𝒜 → B ≠ B' → B ∩ B' = Set.Empty) →
    ∃ (C : Set), ∀ B, B ∈ 𝒜 → ∃! x, x ∈ (C ∩ B)

/-
[Enderton Ch6 §Axiom of Choice, Theorem 6M(5), p.151]
Cardinal comparability (`C ≼ D ∨ D ≼ C`) is intentionally deferred.

Reason: in this project, the cardinal-comparison notation and supporting
injection/equinumerosity layer is planned for dedicated Chapter 6 cardinal
files, not yet part of the current retained Lean subset.
-/

/-- A chain in `𝒜` under subset ordering. -/
def IsSubsetChain (ℬ 𝒜 : Set) : Prop :=
  ℬ ⊆ 𝒜 ∧ ∀ C D, C ∈ ℬ → D ∈ ℬ → C ⊆ D ∨ D ⊆ C

/--
[Enderton Ch6 §Axiom of Choice, Theorem 6M(6), p.151]
Zorn's lemma (subset-order formulation).
-/
def ChoiceSixthForm : Prop :=
  ∀ (𝒜 : Set),
    (∀ (ℬ : Set), IsSubsetChain ℬ 𝒜 → (⋃ ℬ) ∈ 𝒜) →
    ∃ (M : Set), M ∈ 𝒜 ∧ ∀ N, N ∈ 𝒜 → M ⊆ N → N = M

end Choice
end Set
