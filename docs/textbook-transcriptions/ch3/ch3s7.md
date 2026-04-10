# Ch3 Section 7 (Ordering Relations) - Textbook Extraction Draft

Source: Enderton, Chapter 3, pp. 62-65.

## Section Goals

- Formalize linear/total ordering on a carrier set.
- Derive immediate consequences in Theorem 3R:
  1. irreflexivity (`¬ xRx` for `x ∈ A`),
  2. connectedness for distinct points (`xRy ∨ yRx`).

## Formal Statements (Set-Theoretic)

1. Trichotomy on `A`:
   - for each `x,y ∈ A`, one of `xRy`, `x = y`, `yRx` holds, with pairwise exclusion.
2. Linear order on `A`:
   - `R` is a binary relation on `A`,
   - `R` is transitive,
   - trichotomy holds on `A`.
3. Theorem 3R(i):
   - `R` linear order on `A` implies `x ∈ A -> ¬ xRx`.
4. Theorem 3R(ii):
   - `R` linear order on `A` implies for `x,y ∈ A`, `x ≠ y -> (xRy ∨ yRx)`.

## Lean Mapping (Current Repo)

Primary file: `Set/Ch3/S7_OrderingRelations.lean`

- `def TrichotomyOn (R A : Set) : Prop := ...`
- `def IsLinearOrder (R A : Set) : Prop := IsBinaryRelationOn R A ∧ IsTransitiveRel R ∧ TrichotomyOn R A`
- `theorem linear_order_irreflexive (R A : Set) : ...`
- `theorem linear_order_connected (R A : Set) : ...`

## Proof Sketch Notes

- Irreflexive theorem:
  - specialize trichotomy at `(x, x)`,
  - use the contradiction clause `¬(xRx ∧ x = x)`.
- Connectedness theorem:
  - specialize trichotomy at `(x, y)`,
  - eliminate middle branch with `x ≠ y`,
  - keep one of the two relation branches.

