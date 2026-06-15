import Set.Ch3.S6_Equivalence

/-!
# Chapter 3, Section 7: Ordering Relations

Linear orderings and their immediate consequences (Theorem 3R).
-/

namespace Set

/-- [Enderton Ch3 §7, p.62] Condition (b) of the definition of a linear ordering:
"`R` satisfies trichotomy on `A`, by which we mean that for any `x` and `y` in `A`
exactly one of the three alternatives `xRy`, `x = y`, `yRx` holds."

"Exactly one" is spelled out as "at least one of the three" together with "no two
of the three hold simultaneously". -/
def TrichotomyOn (R A : Set) : Prop :=
  ∀ x y, x ∈ A → y ∈ A →
    (⟪x, y⟫ ∈ R ∨ x = y ∨ ⟪y, x⟫ ∈ R) ∧
    ¬(⟪x, y⟫ ∈ R ∧ x = y) ∧
    ¬(⟪x, y⟫ ∈ R ∧ ⟪y, x⟫ ∈ R) ∧
    ¬(x = y ∧ ⟪y, x⟫ ∈ R)

/-- [Enderton Ch3 §7, p.62] "Definition: Let `A` be any set. A linear ordering on
`A` (also called a total ordering on `A`) is a binary relation `R` on `A` (i.e.,
`R ⊆ A ⨯ A`) meeting the following two conditions: (a) `R` is a transitive
relation; i.e., whenever `xRy` and `yRz`, then `xRz`. (b) `R` satisfies trichotomy
on `A` ...." -/
def IsLinearOrder (R A : Set) : Prop :=
  IsBinaryRelationOn R A ∧ IsTransitiveRel R ∧ TrichotomyOn R A

/-- [Enderton Ch3 §7, p.63] "A relation meeting condition (i) is called
*irreflexive*", where condition (i) is Theorem 3R(i): "There is no `x` for which
`xRx`." (Defined just above Theorem 3R so its statement can name this directly;
the textbook introduces the term in the paragraph immediately after the theorem.) -/
def IsIrreflexive (R : Set) : Prop :=
  ∀ x, ⟪x, x⟫ ∉ R

/-- [Enderton Ch3 §7, p.63] "Theorem 3R Let `R` be a linear ordering on `A`.
(i) There is no `x` for which `xRx`." -/
theorem thm_3R_i_linear_order_irreflexive (R A : Set) :
    IsLinearOrder R A → IsIrreflexive R := by
  intro hLin x hxR
  rcases hLin with ⟨hBin, _, hTri⟩
  -- `R ⊆ A ⨯ A`, so `xRx` forces `x ∈ A`; then trichotomy at `(x, x)` excludes it.
  have hxA : x ∈ A := ((Product.Pair.Spec).1 (hBin.2 _ hxR)).1
  rcases hTri x x hxA hxA with ⟨_, hNoEq, _, _⟩
  exact hNoEq ⟨hxR, rfl⟩

/-- [Enderton Ch3 §7, p.63] "one meeting condition (ii) is said to be *connected*
on `A`", where condition (ii) is Theorem 3R(ii): "For distinct `x` and `y` in `A`,
either `xRy` or `yRx`." (Defined just above Theorem 3R; see `IsIrreflexive`.) -/
def IsConnectedOn (R A : Set) : Prop :=
  ∀ x y, x ∈ A → y ∈ A → x ≠ y → (⟪x, y⟫ ∈ R ∨ ⟪y, x⟫ ∈ R)

/-- [Enderton Ch3 §7, p.63] "Theorem 3R Let `R` be a linear ordering on `A`.
(ii) For distinct `x` and `y` in `A`, either `xRy` or `yRx`." -/
theorem thm_3R_ii_linear_order_connected (R A : Set) :
    IsLinearOrder R A → IsConnectedOn R A := by
  intro hLin x y hxA hyA hxy
  rcases hLin with ⟨_, _, hTri⟩
  rcases hTri x y hxA hyA with ⟨hOne, _, _, _⟩
  rcases hOne with hxyR | hEq | hyxR
  · exact Or.inl hxyR
  · exact absurd hEq hxy
  · exact Or.inr hyxR

end Set
