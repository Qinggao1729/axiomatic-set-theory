import Set.Ch3.S2_Relations

namespace Set

/-!
# Chapter 3, Section 3: n-Ary Relations
-/

/-- [Enderton Ch3 §3, p.41] "For triples we define `⟨x, y, z⟩ = ⟨⟨x, y⟩, z⟩`." -/
noncomputable def OrderedTriple (x y z : Set) : Set := ⟪⟪x, y⟫, z⟫

/-- [Enderton Ch3 §3, p.42] "It is convenient for reasons of uniformity to define
also the 1-tuple `⟨x⟩ = x`." -/
def OrderedOneTuple (x : Set) : Set := x

/-- [Enderton Ch3 §3, p.42] Carrier of iterated Kuratowski `n`-tuples over `A`,
supporting "We define an *n-ary relation on A* to be a set of ordered `n`-tuples
with all components in `A`." (helper for `IsNAryRelationOn`). -/
noncomputable def NTupleCarrier : Nat → Set → Set
  | Nat.zero, _ => Set.Empty
  | Nat.succ Nat.zero, A => A
  | Nat.succ (Nat.succ n), A => (NTupleCarrier (Nat.succ n) A) ⨯ A

/-- [Enderton Ch3 §3, p.42] "We define an *n-ary relation on A* to be a set of
ordered `n`-tuples with all components in `A`." -/
def IsNAryRelationOn (n : Nat) (R A : Set) : Prop :=
  R ⊆ NTupleCarrier n A

/--
[Enderton Ch3 §3, p.42] Binary relation on `A`.

Kept as a separate pair-based predicate (instead of reducing to
`IsNAryRelationOn 2 ...`) so later chapters can use the textbook binary-relation
form directly without carrying `Nat`-indexed tuple machinery.
-/
def IsBinaryRelationOn (R A : Set) : Prop :=
  IsRelation R ∧ R ⊆ (A ⨯ A)

end Set
