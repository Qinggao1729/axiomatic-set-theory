# Ch3S3 Textbook Extraction (n-Ary Relations, pp. 41-42)

## Items mapped to Lean

1. Ordered triple
   - Set theory: `⟨x, y, z⟩ = ⟨⟨x, y⟩, z⟩`.
   - Lean: `noncomputable def OrderedTriple (x y z : Set) : Set := ⟪⟪x, y⟫, z⟫`.

2. One-tuple
   - Set theory: `⟨x⟩ = x`.
   - Lean: `def OrderedOneTuple (x : Set) : Set := x`.

3. n-tuple carrier over A
   - Set theory idea: recursive carrier of Kuratowski-style tuples.
   - Lean:
     - `NTupleCarrier 0 A = ∅`
     - `NTupleCarrier 1 A = A`
     - `NTupleCarrier (n+2) A = NTupleCarrier (n+1) A × A`

4. n-ary relation on A
   - Set theory: relation as subset of tuple carrier.
   - Lean: `def IsNAryRelationOn (n : Nat) (R A : Set) : Prop := R ⊆ NTupleCarrier n A`.
