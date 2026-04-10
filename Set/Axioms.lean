/-!
Core axioms and primitive set language.

This file intentionally contains only the primitive layer:
- `Set`, membership notation, subset notation
- core axioms (Enderton Ch2 + infinity)
Derived constructions/theorems belong in `Set/Ch2/S1_Axioms.lean`.
-/

-- Primitive universe of sets
axiom Set : Type

namespace Set

-- Membership and basic predicates
axiom ElementOf : Set → Set → Prop
infix:50 " ∈ " => ElementOf
infix:40 " ∉ " => fun x y => ¬ ElementOf x y

def Nonempty (A : Set) : Prop := ∃ x : Set, x ∈ A

@[simp] def SubsetOf (x a : Set) : Prop := ∀ t : Set, t ∈ x → t ∈ a
infix:50 " ⊆ " => SubsetOf


-- [Enderton Ch2 §Axioms, p.17] Extensionality axiom
axiom extensionality : ∀ A B : Set, (∀ x : Set, x ∈ A ↔ x ∈ B) → A = B

-- [Enderton Ch2 §Axioms, p.18] Empty set axiom
axiom empty : ∃ B : Set, ∀ x : Set, x ∉ B

-- [Enderton Ch2 §Axioms, p.18] Pairing axiom
axiom pairing : ∀ u v : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x = u ∨ x = v

-- [Enderton Ch2 §Axioms, p.18] Union axiom (preliminary binary form)
axiom union_preliminary : ∀ a b : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ∈ a ∨ x ∈ b

-- [Enderton Ch2 §Axioms, p.18] Power set axiom
axiom power : ∀ a : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ⊆ a

-- [Enderton Ch2 §Axioms, p.21] Subset/Comprehension schema
axiom comprehension (P : Set → Prop) (c : Set) :
  ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ∈ c ∧ P x

-- [Enderton Ch2 §Arbitrary Unions and Intersections, p.24] Full union axiom
axiom union : ∀ A : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ ∃ b : Set, b ∈ A ∧ x ∈ b

-- [Enderton Ch4 §Inductive Sets, p.68] Infinity axiom (primitive form)
axiom infinity :
  ∃ A : Set,
    (∃ e : Set, (∀ x : Set, x ∉ e) ∧ e ∈ A) ∧
    (∀ a : Set, a ∈ A → ∃ s : Set, (∀ x : Set, x ∈ s ↔ x ∈ a ∨ x = a) ∧ s ∈ A)

end Set
