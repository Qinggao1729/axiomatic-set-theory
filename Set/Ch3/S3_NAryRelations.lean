import Set.Ch3.S2_Relations

namespace Set

/-!
# Chapter 3, Section 3: n-Ary Relations
-/

-- Enderton p.41–42: ordered triples by iteration of ordered pairs.

noncomputable def OrderedTriple (x y z : Set) : Set := ⟪⟪x, y⟫, z⟫

-- Enderton p.42: for uniformity, 1-tuple is the object itself.
def OrderedOneTuple (x : Set) : Set := x

-- Carrier set for iterated Kuratowski n-tuples over A.
noncomputable def NTupleCarrier : Nat → Set → Set
  | Nat.zero, _ => Set.Empty
  | Nat.succ Nat.zero, A => A
  | Nat.succ (Nat.succ n), A => (NTupleCarrier (Nat.succ n) A) ⨯ A

-- A set of n-tuples whose coordinates lie in A.
def IsNAryRelationOn (n : Nat) (R A : Set) : Prop :=
  R ⊆ NTupleCarrier n A

end Set
