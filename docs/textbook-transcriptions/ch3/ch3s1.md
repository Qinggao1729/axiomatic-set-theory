# Ch3S1 Textbook Extraction (Ordered Pairs, pp. 35-38)

This temporary note records the textbook-to-Lean mapping before/alongside formalization.

## Items

1. Definition: ordered pair
   - Set theory: `⟨x, y⟩ = {x, {x, y}}`
   - Lean target: `OrderedPair`, `OrderedPair.Spec`, notation `⟪x, y⟫`

2. Theorem 3A (uniqueness)
   - Set theory: `⟨u, v⟩ = ⟨x, y⟩ ↔ (u = x ∧ v = y)`
   - Lean target: `OrderedPair.uniqueness`
   - Human sketch:
     - Forward: extract `Singleton u` and `Pair u v` memberships from equality, then split cases.
     - Backward: substitute equal components and close by reflexivity/spec simplification.

3. Lemma 3B
   - Set theory: if `x ∈ C` and `y ∈ C` then `⟨x, y⟩ ∈ 𝒫𝒫 C`
   - Lean target: `OrderedPair.in_power_power`
   - Human sketch: show both members in `C`, conclude each component is subset of `C`.

4. Corollary 3C / Product construction
   - Set theory: existence of a set containing exactly pairs with first component in `A`, second in `B`.
   - Lean targets: `OrderedPair.product`, `Product`, `Product.Spec`
   - Human sketch: use comprehension over `𝒫𝒫 (A ∪ B)` with predicate "is an ordered pair from `A × B`".
