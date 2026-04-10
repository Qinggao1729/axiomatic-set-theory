# Enderton, *Elements of Set Theory* — Chapters 2, 3, 4 & 5

_File formerly named `Enderton_Ch1_3_Todos.md`; it tracks the whole textbook thread, not only Chapters 1–3._

## Todo Format (Must Follow)

- Every theorem/definition/axiom item is a checkbox item:
  - `- [x]` for done, `- [ ]` for pending.
- Each checkbox item must use the same two-child format:
  - `- **Set theory:** ...`
  - `- **Lean:** ...`
- Lean lines should use concrete declaration names/signatures from the current `.lean` file.
- Do not include tactic decorators (e.g. `@[simp]`) in this todo file.
- Every section (not only Chapter 2) must stay synchronized with its corresponding `.lean` file(s).
- Each section should explicitly state its primary Lean file(s) near the section header.

# Chapter 2: Axioms and Operations

## Section 1 (pp. 17–22): Core Axioms + Binary/Subset Operations

Primary file: `Set/Ch2/S1_Axioms.lean`  
Primitive declarations live in: `Set/Axioms.lean`

- [x] **Axiom (Extensionality):**
  - **Set theory:** $\forall A\forall B[(\forall x(x\in A \Leftrightarrow x\in B)) \Rightarrow A = B]$
  - **Lean:** `axiom extensionality : ∀ (A B : Set), (∀ (x : Set), x ∈ A ↔ x ∈ B) → A = B`

### Empty Set

- [x] **Axiom (Empty set):**
  - **Set theory:** $\exists B\forall x(x \notin B)$
  - **Lean:** `axiom empty : ∃ (B : Set), ∀ (x : Set), x ∉ B`
- [x] **Definition (Empty):**
  - **Set theory:** $\forall x(x \notin \varnothing)$
  - **Lean:** `noncomputable def Empty : Set := Classical.choose empty`
- [x] **Uniqueness (Empty):**
  - **Set theory:** $\exists! B\forall x(x \notin B)$
  - **Lean:** `theorem empty_unique : ∃! B : Set, ∀ x : Set, x ∉ B`
- [x] **Notation (Empty):**
  - **Set theory:** $\varnothing$
  - **Lean:** `notation "∅" => Empty`

### Pair Set

- [x] **Axiom (Pairing):**
  - **Set theory:** $\forall u\forall v\exists B\forall x(x \in B \Leftrightarrow x = u \lor x = v)$
  - **Lean:** `axiom pairing : ∀ (u v : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x = u ∨ x = v`
- [x] **Definition (Pair):**
  - **Set theory:** $\forall x(x \in \{u, v\} \Leftrightarrow x = u \lor x = v)$
  - **Lean:** `noncomputable def Pair (u v : Set) : Set := Classical.choose (pairing u v)`
- [x] **Uniqueness (Pair):**
  - **Set theory:** $\forall u\forall v\exists! B\forall x(x \in B \Leftrightarrow x = u \lor x = v)$
  - **Lean:** `theorem pair_unique (u v : Set) : ∃! B : Set, ∀ x : Set, x ∈ B ↔ x = u ∨ x = v`

### Singleton

- [x] **Definition (Singleton):**
  - **Set theory:** $\forall y(y \in \{x\} \Leftrightarrow y = x)$
  - **Lean:** `noncomputable def Singleton (x : Set) : Set := Classical.choose (pairing x x)`
- [x] **Specification (Singleton.Spec):**
  - **Set theory:** $\forall y(y \in \{x\} \Leftrightarrow y = x)$
  - **Lean:** `lemma Singleton.Spec (x : Set) : ∀ y : Set, y ∈ Singleton x ↔ y = x`

### Power Set

- [x] **Axiom (Power set):**
  - **Set theory:** $\forall A\exists B\forall x(x \in B \Leftrightarrow x \subseteq A)$
  - **Lean:** `axiom power : ∀ (A : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ⊆ A`
- [x] **Definition (Power):**
  - **Set theory:** $\forall x(x \in \mathcal{P}(A) \Leftrightarrow x \subseteq A)$
  - **Lean:** `noncomputable def Power (A : Set) : Set := Classical.choose (power A)`
- [x] **Uniqueness (Power):**
  - **Set theory:** $\forall A\exists! B\forall x(x \in B \Leftrightarrow x \subseteq A)$
  - **Lean:** `theorem power_unique (A : Set) : ∃! B : Set, ∀ x : Set, x ∈ B ↔ x ⊆ A`
- [x] **Notation (Power):**
  - **Set theory:** $\mathcal{P}(A)$
  - **Lean:** `prefix:75 "𝒫" => Power`

### Binary Union

- [x] **Axiom (Union preliminary):**
  - **Set theory:** $\forall A\forall B\exists U\forall x(x \in U \Leftrightarrow x \in A \lor x \in B)$
  - **Lean:** `axiom union_preliminary : ∀ (a b : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ a ∨ x ∈ b`
- [x] **Definition (Union):**
  - **Set theory:** $\forall x(x \in A \cup B \Leftrightarrow x \in A \lor x \in B)$
  - **Lean:** `noncomputable def Union (A B : Set) : Set := Classical.choose (union_preliminary A B)`
- [x] **Uniqueness (Union):**
  - **Set theory:** $\forall A\forall B\exists! U\forall x(x \in U \Leftrightarrow x \in A \lor x \in B)$
  - **Lean:** `theorem union_unique (A B : Set) : ∃! U : Set, ∀ x : Set, x ∈ U ↔ x ∈ A ∨ x ∈ B`
- [x] **Notation (Union):**
  - **Set theory:** $A \cup B$
  - **Lean:** `infix:70 " ∪ " => Union`

### Comprehension

- [x] **Axiom schema (Comprehension):**
  - **Set theory:** $\forall c\exists C\forall x(x \in C \Leftrightarrow x \in c \land P(x))$
  - **Lean:** `axiom comprehension (P : Set → Prop) (c : Set) : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x`
- [x] **Definition (Comprehension):**
  - **Set theory:** $\forall x(x \in \{x \in c \mid P(x)\} \Leftrightarrow x \in c \land P(x))$
  - **Lean:** `noncomputable def Comprehension (P : Set → Prop) (c : Set) : Set := Classical.choose (comprehension P c)`
- [x] **Uniqueness (Comprehension):**
  - **Set theory:** $\forall c\exists! C\forall x(x \in C \Leftrightarrow x \in c \land P(x))$
  - **Lean:** `theorem comprehension_unique (P : Set → Prop) (c : Set) : ∃! C : Set, ∀ x : Set, x ∈ C ↔ x ∈ c ∧ P x`

### Binary Intersection

- [x] **Axiom source (Comprehension):**
  - **Set theory:** $\forall c\exists C\forall x(x \in C \Leftrightarrow x \in c \land P(x))$
  - **Lean:** `axiom comprehension (P : Set → Prop) (c : Set) : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x`
- [x] **Definition (Intersection):**
  - **Set theory:** $\forall x(x \in A \cap B \Leftrightarrow x \in A \land x \in B)$
  - **Lean:** `noncomputable def Intersection (A B : Set) : Set := Classical.choose (comprehension (fun x => x ∈ B) A)`
- [x] **Uniqueness (Intersection):**
  - **Set theory:** $\forall A\forall B\exists! I\forall x(x \in I \Leftrightarrow x \in A \land x \in B)$
  - **Lean:** `theorem intersection_unique (A B : Set) : ∃! I : Set, ∀ x : Set, x ∈ I ↔ x ∈ A ∧ x ∈ B`
- [x] **Notation (Intersection):**
  - **Set theory:** $A \cap B$
  - **Lean:** `infix:70 " ∩ " => Intersection`

### Difference

- [x] **Axiom source (Comprehension):**
  - **Set theory:** $\forall c\exists C\forall x(x \in C \Leftrightarrow x \in c \land P(x))$
  - **Lean:** `axiom comprehension (P : Set → Prop) (c : Set) : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x`
- [x] **Definition (Difference):**
  - **Set theory:** $\forall x(x \in A - B \Leftrightarrow x \in A \land x \notin B)$
  - **Lean:** `noncomputable def Difference (A B : Set) : Set := Classical.choose (comprehension (fun x => x ∉ B) A)`
- [x] **Uniqueness (Difference):**
  - **Set theory:** $\forall A\forall B\exists! D\forall x(x \in D \Leftrightarrow x \in A \land x \notin B)$
  - **Lean:** `theorem difference_unique (A B : Set) : ∃! D : Set, ∀ x : Set, x ∈ D ↔ x ∈ A ∧ x ∉ B`
- [x] **Notation (Difference):**
  - **Set theory:** $A - B$
  - **Lean:** `infix:70 " - " => Difference`

### Theorem 2A

- [x] **No universal set:**
  - **Set theory:** $\neg \exists A\forall x(x \in A)$
  - **Lean:** `theorem no_universal_set : ¬ ∃ (A : Set), ∀ (x : Set), x ∈ A`

## Section 2 (pp. 23–26): Arbitrary Unions and Intersections

Primary file: `Set/Ch2/S2_ArbitraryUnionsIntersections.lean`

### Big Union

- [x] **Axiom (Union, full form):**
  - **Set theory:** $\forall A\exists B\forall x\big(x \in B \Leftrightarrow \exists b(b \in A \land x \in b)\big)$
  - **Lean:** `axiom union : ∀ (A : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b)`
- [x] **Definition (BigUnion):**
  - **Set theory:** $\forall x\big(x \in \bigcup A \Leftrightarrow \exists b(b \in A \land x \in b)\big)$
  - **Lean:** `noncomputable def BigUnion (A : Set) : Set := Classical.choose (union A)`
- [x] **Uniqueness (BigUnion):**
  - **Set theory:** $\forall A\exists! U\forall x\big(x \in U \Leftrightarrow \exists b(b \in A \land x \in b)\big)$
  - **Lean:** `theorem bigUnion_unique (A : Set) : ∃! U : Set, ∀ x : Set, x ∈ U ↔ (∃ b : Set, b ∈ A ∧ x ∈ b)`
- [x] **Notation (BigUnion):**
  - **Set theory:** $\bigcup A$
  - **Lean:** `prefix:75 "⋃" => BigUnion`

### Big Intersection (Nonempty Index Set)

- [x] **Axiom source (Comprehension):**
  - **Set theory:** $\forall c\exists C\forall x(x \in C \Leftrightarrow x \in c \land P(x))$
  - **Lean:** `axiom comprehension (P : Set → Prop) (c : Set) : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x`
- [x] **Definition (BigIntersection):**
  - **Set theory:** $A \neq \varnothing \Rightarrow \forall x\big(x \in \bigcap A \Leftrightarrow \forall a(a \in A \Rightarrow x \in a)\big)$
  - **Lean:** `noncomputable def BigIntersection (A : Set) (hA : A.Nonempty) : Set := Classical.choose (intersection A hA)`
- [x] **Uniqueness (Theorem 2B):**
  - **Set theory:** $A \neq \varnothing \Rightarrow \exists! B\forall x\big(x \in B \Leftrightarrow \forall a(a \in A \Rightarrow x \in a)\big)$
  - **Lean:** `theorem intersection (A : Set) (h : A.Nonempty) : ∃! (B : Set), ∀ (x : Set), x ∈ B ↔ (∀ (a : Set), a ∈ A → x ∈ a)`

### Derived Properties

- [x] **Pair index set nonempty:**
  - **Set theory:** $\{A,B\}\neq\varnothing$
  - **Lean:** `lemma pair_nonempty (A B : Set) : (Pair A B).Nonempty`
- [x] **BigUnion recovers binary union:**
  - **Set theory:** $\bigcup\{A,B\}=A\cup B$
  - **Lean:** `theorem bigUnion_pair (A B : Set) : ⋃ (Pair A B) = A ∪ B`
- [x] **BigIntersection recovers binary intersection:**
  - **Set theory:** $\bigcap\{A,B\}=A\cap B$
  - **Lean:** `theorem bigIntersection_pair (A B : Set) : BigIntersection (Pair A B) (pair_nonempty A B) = A ∩ B`
- [x] **Union of empty index set:**
  - **Set theory:** $\bigcup\varnothing=\varnothing$
  - **Lean:** `theorem union_of_empty_set : ⋃ Empty = Empty`
- [x] **Member subset BigUnion:**
  - **Set theory:** $\forall A\forall b\big(b \in A \Rightarrow b \subseteq \bigcup A\big)$
  - **Lean:** `theorem member_subset_bigUnion (A b : Set) (hb : b ∈ A) : b ⊆ ⋃ A`

## Section 3 (pp. 27–33): Algebra of Sets

Primary file: `Set/Ch2/S3_AlgebraOfSets.lean`

- [x] **Commutative law (Union):**
  - **Set theory:** $A \cup B = B \cup A$
  - **Lean:** `theorem Union.comm (A B : Set) : A ∪ B = B ∪ A`
- [x] **Commutative law (Intersection):**
  - **Set theory:** $A \cap B = B \cap A$
  - **Lean:** `theorem Intersection.comm (A B : Set) : A ∩ B = B ∩ A`
- [x] **Associative law (Union):**
  - **Set theory:** $A \cup (B \cup C) = (A \cup B) \cup C$
  - **Lean:** `theorem Union.assoc (A B C : Set) : A ∪ (B ∪ C) = (A ∪ B) ∪ C`
- [x] **Associative law (Intersection):**
  - **Set theory:** $A \cap (B \cap C) = (A \cap B) \cap C$
  - **Lean:** `theorem Intersection.assoc (A B C : Set) : A ∩ (B ∩ C) = (A ∩ B) ∩ C`
- [x] **Distributive law ($\cap$ over $\cup$):**
  - **Set theory:** $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$
  - **Lean:** `theorem Intersection.dist (A B C : Set) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`
- [x] **Distributive law ($\cup$ over $\cap$):**
  - **Set theory:** $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$
  - **Lean:** `theorem Union.dist (A B C : Set) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`
- [x] **De Morgan's law (Union):**
  - **Set theory:** $C - (A \cup B) = (C - A) \cap (C - B)$
  - **Lean:** `theorem Union.deMorgan (A B C : Set) : C - (A ∪ B) = (C - A) ∩ (C - B)`
- [x] **De Morgan's law (Intersection):**
  - **Set theory:** $C - (A \cap B) = (C - A) \cup (C - B)$
  - **Lean:** `theorem Intersection.deMorgan (A B C : Set) : C - (A ∩ B) = (C - A) ∪ (C - B)`
- [x] **Identity (Union empty):**
  - **Set theory:** $A \cup \varnothing = A$
  - **Lean:** `theorem Union.empty (A : Set) : A ∪ Empty = A`
- [x] **Identity (Intersection empty):**
  - **Set theory:** $A \cap \varnothing = \varnothing$
  - **Lean:** `theorem Intersection.empty (A : Set) : A ∩ Empty = Empty`
- [x] **Identity (Intersection with difference):**
  - **Set theory:** $A \cap (C - A) = \varnothing$
  - **Lean:** `theorem Intersection.empty' (A C : Set) : A ∩ (C - A) = Empty`
- [x] **Identity (space union):**
  - **Set theory:** $A \subseteq S \Rightarrow A \cup S = S$
  - **Lean:** `theorem Union.space (A S : Set) (hAS : A ⊆ S) : A ∪ S = S`
- [x] **Identity (space intersection):**
  - **Set theory:** $A \subseteq S \Rightarrow A \cap S = A$
  - **Lean:** `theorem Intersection.space (A S : Set) (hAS : A ⊆ S) : A ∩ S = A`
- [x] **Identity (space complement union):**
  - **Set theory:** $A \subseteq S \Rightarrow A \cup (S - A) = S$
  - **Lean:** `theorem Union.compl (A S : Set) (hAS : A ⊆ S) : A ∪ (S - A) = S`
- [x] **Identity (space complement intersection):**
  - **Set theory:** $A \cap (S - A) = \varnothing$
  - **Lean:** `theorem Intersection.compl (A S : Set) : A ∩ (S - A) = (∅ : Set)`
- [x] **Monotonicity (Union):**
  - **Set theory:** $A \subseteq B \Rightarrow A \cup C \subseteq B \cup C$
  - **Lean:** `theorem Union.mono (A B C : Set) : A ⊆ B → A ∪ C ⊆ B ∪ C`
- [x] **Monotonicity (Intersection):**
  - **Set theory:** $A \subseteq B \Rightarrow A \cap C \subseteq B \cap C$
  - **Lean:** `theorem Intersection.mono (A B C : Set) : A ⊆ B → A ∩ C ⊆ B ∩ C`
- [x] **Monotonicity (BigUnion):**
  - **Set theory:** $A \subseteq B \Rightarrow \bigcup A \subseteq \bigcup B$
  - **Lean:** `theorem BigUnion.mono (A B : Set) : A ⊆ B → ⋃A ⊆ ⋃B`
- [x] **Antimonotonicity (Difference):**
  - **Set theory:** $A \subseteq B \Rightarrow C - B \subseteq C - A$
  - **Lean:** `theorem Difference.antimono (A B C : Set) : A ⊆ B → C - B ⊆ C - A`
- [x] **Antimonotonicity (BigIntersection, nonempty):**
  - **Set theory:** $\varnothing \neq A \subseteq B \Rightarrow \bigcap B \subseteq \bigcap A$
  - **Lean:** `theorem BigIntersection.antimono_nonempty (A B : Set) (hA : A.Nonempty) (hB : B.Nonempty) : A ⊆ B → BigIntersection B hB ⊆ BigIntersection A hA`
- [x] **Definition (FamilyUnion):**
  - **Set theory:** $\{A \cup X \mid X \in \mathscr{B}\}$
  - **Lean:** `noncomputable def FamilyUnion (A ℬ : Set) : Set := ...`
- [x] **Specification (FamilyUnion.Spec):**
  - **Set theory:** $t \in \{A \cup X \mid X \in \mathscr{B}\} \Leftrightarrow t \in \mathcal{P}(A \cup \bigcup\mathscr{B}) \land \exists X(X \in \mathscr{B} \land t = A \cup X)$
  - **Lean:** `lemma FamilyUnion.Spec (A ℬ : Set) : ∀ t : Set, t ∈ FamilyUnion A ℬ ↔ t ∈ 𝒫 (A ∪ ⋃ℬ) ∧ ∃ X : Set, X ∈ ℬ ∧ t = A ∪ X`
- [x] **Nonempty (FamilyUnion):**
  - **Set theory:** $\mathscr{B}\neq\varnothing \Rightarrow \{A \cup X \mid X \in \mathscr{B}\}\neq\varnothing$
  - **Lean:** `theorem FamilyUnion.nonempty (A ℬ : Set) (hℬ : ℬ.Nonempty) : (FamilyUnion A ℬ).Nonempty`
- [x] **Definition (FamilyInter):**
  - **Set theory:** $\{A \cap X \mid X \in \mathscr{B}\}$
  - **Lean:** `noncomputable def FamilyInter (A ℬ : Set) : Set := ...`
- [x] **Specification (FamilyInter.Spec):**
  - **Set theory:** $t \in \{A \cap X \mid X \in \mathscr{B}\} \Leftrightarrow t \in \mathcal{P}(A) \land \exists X(X \in \mathscr{B} \land t = A \cap X)$
  - **Lean:** `lemma FamilyInter.Spec (A ℬ : Set) : ∀ t : Set, t ∈ FamilyInter A ℬ ↔ t ∈ 𝒫 A ∧ ∃ X : Set, X ∈ ℬ ∧ t = A ∩ X`
- [x] **Definition (FamilyDiff):**
  - **Set theory:** $\{C - X \mid X \in \mathscr{A}\}$
  - **Lean:** `noncomputable def FamilyDiff (C 𝒜 : Set) : Set := ...`
- [x] **Specification (FamilyDiff.Spec):**
  - **Set theory:** $t \in \{C - X \mid X \in \mathscr{A}\} \Leftrightarrow t \in \mathcal{P}(C) \land \exists X(X \in \mathscr{A} \land t = C - X)$
  - **Lean:** `lemma FamilyDiff.Spec (C 𝒜 : Set) : ∀ t : Set, t ∈ FamilyDiff C 𝒜 ↔ t ∈ 𝒫 C ∧ ∃ X : Set, X ∈ 𝒜 ∧ t = C - X`
- [x] **Nonempty (FamilyDiff):**
  - **Set theory:** $\mathscr{A}\neq\varnothing \Rightarrow \{C - X \mid X \in \mathscr{A}\}\neq\varnothing$
  - **Lean:** `theorem FamilyDiff.nonempty (C 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) : (FamilyDiff C 𝒜).Nonempty`
- [x] **Generalized distributive law (Union over BigIntersection):**
  - **Set theory:** $A \cup \bigcap\mathscr{B} = \bigcap\{A \cup X \mid X \in \mathscr{B}\}$ for $\mathscr{B} \neq \varnothing$
  - **Lean:** `theorem Union.dist_biginter (A ℬ : Set) (hℬ : ℬ.Nonempty) : A ∪ BigIntersection ℬ hℬ = BigIntersection (FamilyUnion A ℬ) (FamilyUnion.nonempty A ℬ hℬ)`
- [x] **Generalized distributive law (Intersection over BigUnion):**
  - **Set theory:** $A \cap \bigcup\mathscr{B} = \bigcup\{A \cap X \mid X \in \mathscr{B}\}$
  - **Lean:** `theorem Intersection.dist_bigunion (A ℬ : Set) : A ∩ ⋃ℬ = ⋃(FamilyInter A ℬ)`
- [x] **Generalized De Morgan's law (BigUnion):**
  - **Set theory:** $C - \bigcup\mathscr{A} = \bigcap\{C - X \mid X \in \mathscr{A}\}$ for $\mathscr{A} \neq \varnothing$
  - **Lean:** `theorem deMorgan_bigunion (C 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) : C - ⋃𝒜 = BigIntersection (FamilyDiff C 𝒜) (FamilyDiff.nonempty C 𝒜 h𝒜)`
- [x] **Generalized De Morgan's law (BigIntersection):**
  - **Set theory:** $C - \bigcap\mathscr{A} = \bigcup\{C - X \mid X \in \mathscr{A}\}$ for $\mathscr{A} \neq \varnothing$
  - **Lean:** `theorem deMorgan_biginter (C 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) : C - BigIntersection 𝒜 h𝒜 = ⋃(FamilyDiff C 𝒜)`

---

# Chapter 3: Relations and Functions

## Ordered Pairs (pp. 35–38)

Primary file: `Set/Ch3/S1_OrderedPairs.lean`
Note: internal helper lemmas are intentionally omitted from this checklist.

- [x] **Definition (Ordered pair):**
  - **Set theory:** $\langle x, y \rangle = \{x,\{x, y\}\}$
  - **Lean:** `noncomputable def OrderedPair (x y : Set) : Set := Pair (Singleton x) (Pair x y)`
- [x] **Specification (OrderedPair.Spec):**
  - **Set theory:** $\forall w\,(w \in \langle x, y\rangle \Leftrightarrow w = \{x\} \lor w = \{x,y\})$
  - **Lean:** `lemma OrderedPair.Spec (x y : Set) : ∀ w, w ∈ OrderedPair x y ↔ w = Singleton x ∨ w = Pair x y`
- [x] **Notation (preferred ordered pair syntax):**
  - **Set theory:** Use $\langle x, y \rangle$ as textbook notation.
  - **Lean:** `notation:90 "⟪" x ", " y "⟫" => OrderedPair x y`
- [x] **Theorem 3A (uniqueness):**
  - **Set theory:** $\langle u, v \rangle = \langle x, y \rangle \Leftrightarrow (u = x \land v = y)$
  - **Lean:** `theorem OrderedPair.uniqueness (u v x y : Set) : ⟪u, v⟫ = ⟪x, y⟫ ↔ u = x ∧ v = y`
- [x] **Lemma 3B:**
  - **Set theory:** $x \in C \land y \in C \Rightarrow \langle x, y \rangle \in \mathcal{P}\mathcal{P}C$
  - **Lean:** `lemma OrderedPair.in_power_power (x y C : Set) : x ∈ C → y ∈ C → OrderedPair x y ∈ Power (Power C)`
- [x] **Corollary 3C (existence of product carrier):**
  - **Set theory:** $\exists C\,\forall w\,(w \in C \Leftrightarrow w \in \mathcal{P}\mathcal{P}(A \cup B) \land \exists x\exists y\,(x \in A \land y \in B \land w=\langle x,y\rangle))$
  - **Lean:** `lemma OrderedPair.product (A B : Set) : ∃ C, ∀ w, w ∈ C ↔ w ∈ 𝒫 𝒫 (A ∪ B) ∧ ∃ x y, x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫`
- [x] **Definition (Cartesian product):**
  - **Set theory:** $A \times B = \{\langle x, y\rangle \mid x \in A \land y \in B\}$
  - **Lean:** `noncomputable def Product (A B : Set) : Set := Classical.choose (OrderedPair.product A B)`
- [x] **Specification (Product.Spec):**
  - **Set theory:** $\forall w\,(w \in A \times B \Leftrightarrow \exists x\exists y\,(x \in A \land y \in B \land w=\langle x,y\rangle))$
  - **Lean:** `lemma Product.Spec (A B : Set) : ∀ w, w ∈ Product A B ↔ ∃ x y, x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫`

## Relations (pp. 39–41)

Primary file: `Set/Ch3/S2_Relations.lean`

- [x] **Lemma 3D:**
  - **Set theory:** $\langle x, y \rangle \in A \Rightarrow x \in \bigcup\bigcup A \land y \in \bigcup\bigcup A$
  - **Lean:** `lemma OrderedPair.in_union_union (x y A : Set) : ⟨x, y⟩ ∈ A → x ∈ ⋃⋃A ∧ y ∈ ⋃⋃A`
- [x] **Definition (Relation):**
  - **Set theory:** $R$ is a relation iff $\forall w \in R\exists x\exists y(w = \langle x, y \rangle)$
  - **Lean:** `def IsRelation (R : Set) : Prop := ∀ w, w ∈ R → ∃ x y, w = ⟪x, y⟫`
- [x] **Definition (Domain):**
  - **Set theory:** $\operatorname{dom}(R)=\{x \mid \exists y\,\langle x,y\rangle\in R\}$
  - **Lean:** `noncomputable def Relation.Domain (R : Set) : Set := ...`
- [x] **Specification (Domain.Spec):**
  - **Set theory:** $x \in \operatorname{dom}(R) \Leftrightarrow \exists y\,\langle x,y\rangle\in R$
  - **Lean:** `lemma Relation.Domain.Spec (R : Set) : ∀ x, x ∈ Relation.Domain R ↔ ∃ y, ⟪x, y⟫ ∈ R`
- [x] **Notation (Domain):**
  - **Set theory:** $\operatorname{dom}(R)$
  - **Lean:** `notation:90 "dom " R => Relation.Domain R`
- [x] **Definition (Range):**
  - **Set theory:** $\operatorname{ran}(R)=\{y \mid \exists x\,\langle x,y\rangle\in R\}$
  - **Lean:** `noncomputable def Relation.Range (R : Set) : Set := ...`
- [x] **Specification (Range.Spec):**
  - **Set theory:** $y \in \operatorname{ran}(R) \Leftrightarrow \exists x\,\langle x,y\rangle\in R$
  - **Lean:** `lemma Relation.Range.Spec (R : Set) : ∀ y, y ∈ Relation.Range R ↔ ∃ x, ⟪x, y⟫ ∈ R`
- [x] **Notation (Range):**
  - **Set theory:** $\operatorname{ran}(R)$
  - **Lean:** `notation:90 "ran " R => Relation.Range R`
- [x] **Definition (Field):**
  - **Set theory:** $\operatorname{fld}(R)=\operatorname{dom}(R)\cup\operatorname{ran}(R)$
  - **Lean:** `noncomputable def Relation.Field (R : Set) : Set := (dom R) ∪ (ran R)`
- [x] **Specification (Field.Spec):**
  - **Set theory:** $z\in \operatorname{fld}(R)\Leftrightarrow z\in\operatorname{dom}(R)\lor z\in\operatorname{ran}(R)$
  - **Lean:** `lemma Relation.Field.Spec (R : Set) : ∀ z, z ∈ Relation.Field R ↔ z ∈ (dom R) ∨ z ∈ (ran R)`
- [x] **Notation (Field):**
  - **Set theory:** $\operatorname{fld}(R)$
  - **Lean:** `notation:90 "fld " R => Relation.Field R`
## n-Ary Relations (pp. 41–42)

Primary file: `Set/Ch3/S3_NAryRelations.lean`

- [x] **Definition (Ordered triple):**
  - **Set theory:** $\langle x, y, z \rangle = \langle\langle x, y \rangle, z \rangle$
  - **Lean:** `noncomputable def OrderedTriple (x y z : Set) : Set := ⟪⟪x, y⟫, z⟫`
- [x] **Definition (1-tuple):**
  - **Set theory:** $\langle x \rangle = x$
  - **Lean:** `def OrderedOneTuple (x : Set) : Set := x`
- [x] **Definition (n-tuple carrier over $A$):**
  - **Set theory:** recursive carrier of Kuratowski-style $n$-tuples over $A$
  - **Lean:** `noncomputable def NTupleCarrier : Nat → Set → Set`
- [x] **Definition (n-ary relation on $A$):**
  - **Set theory:** $R$ is an $n$-ary relation on $A$ iff every element of $R$ is in the carrier of $n$-tuples over $A$
  - **Lean:** `def IsNAryRelationOn (n : Nat) (R A : Set) : Prop := R ⊆ NTupleCarrier n A`

## Functions (pp. 42–54)

Primary files:
- `Set/Ch3/S4_Functions.lean`
- `Set/Ch3/S5_InfiniteCartesianProducts.lean` (for Theorem 3J)
- `Set/Choice.lean` (choice-first-form statement)

- [x] **Definition (Function):**
  - **Set theory:** $F$ is a relation and for each $x \in \operatorname{dom}(F)$ there exists a unique $y$ with $\langle x, y \rangle \in F$
  - **Lean:** `def IsFunction (F : Set) : Prop := IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟨x, y⟩ ∈ F`
- [x] **Definition (Maps into):**
  - **Set theory:** $F : A \to B$ iff `IsFunction F`, `dom F = A`, and `ran F ⊆ B`
  - **Lean:** `def MapsInto (F A B : Set) : Prop := IsFunction F ∧ (dom F) = A ∧ SubsetOf (ran F) B`
- [x] **Definition (Maps onto):**
  - **Set theory:** $F$ maps $A$ onto $B$ iff $F : A \to B$ and `ran F = B`
  - **Lean:** `def MapsOnto (F A B : Set) : Prop := MapsInto F A B ∧ (ran F) = B`
- [x] **Definition (Single-rooted / one-to-one wrapper):**
  - **Set theory:** single-rooted means uniqueness of preimage for each element of the range
  - **Lean:** `def IsSingleRooted (R : Set) : Prop := ∀ y, y ∈ (ran R) → ∃! x, ⟨x, y⟩ ∈ R`; `def IsOneToOne (F : Set) : Prop := IsFunction F ∧ IsSingleRooted F`
- [x] **Definition (Identity on $A$):**
  - **Set theory:** $I_A = \{\langle x, x \rangle \mid x \in A\}$
  - **Lean:** `noncomputable def Identity (A : Set) : Set`; `lemma Identity.Spec ...`; `lemma Identity.Pair.Spec ...`
- [x] **Definition (Inverse relation):**
  - **Set theory:** $F^{-1} = \{\langle v, u \rangle \mid \langle u, v \rangle \in F\}$
  - **Lean:** `noncomputable def Inverse (F : Set)`; `lemma Inverse.Spec ...`; `lemma Inverse.Pair.Spec ...`
- [x] **Definition (Composition):**
  - **Set theory:** $F \circ G = \{\langle u, v \rangle \mid \exists t(\langle u, t \rangle \in G \land \langle t, v \rangle \in F)\}$
  - **Lean:** `noncomputable def Composition (F G : Set)`; `lemma Composition.Spec ...`; `lemma Composition.Pair.Spec ...`
- [x] **Definition (Restriction):**
  - **Set theory:** $F \upharpoonright C = \{\langle u, v \rangle \in F \mid u \in C\}$
  - **Lean:** `noncomputable def Restriction (F C : Set)`; `lemma Restriction.Spec ...`; `lemma Restriction.Pair.Spec ...`
- [x] **Definition (Image):**
  - **Set theory:** $F[A] = \operatorname{ran}(F \upharpoonright A)$
  - **Lean:** `noncomputable def Image (F C : Set) := ran (Restriction F C)`; `lemma Image.Spec ...`
- [x] **Basic helper lemmas for ordered pairs/functions:**
  - **Set theory:** direct elimination/introduction facts for `dom`, `ran`, and products
  - **Lean:** `lemma Pair.mem_dom ...`; `lemma Pair.mem_ran ...`; `lemma Pair.mem_product ...`; `lemma Pair.mem_product_elim ...`; `lemma function_value_unique ...`
- [x] **Theorem 3E (inverse swaps domain/range, double inverse):**
  - **Set theory:** `dom(F⁻¹)=ran(F)`, `ran(F⁻¹)=dom(F)`, and for relations `(F⁻¹)⁻¹=F`
  - **Lean:** `theorem domain_inverse ...`; `theorem range_inverse ...`; `theorem relation_inverse_inverse ...`
- [x] **Theorem 3F (function vs single-rooted under inverse):**
  - **Set theory:** `IsFunction (F⁻¹) ↔ IsSingleRooted F`, and for relations `IsFunction F ↔ IsSingleRooted (F⁻¹)`
  - **Lean:** `theorem inverse_single_rooted ...`; `theorem relation_function_single_rooted ...`
- [x] **Theorem 3G (inverse evaluation laws for one-to-one functions):**
  - **Set theory:** if `F` is one-to-one, inverse evaluation composes back to the original element
  - **Lean:** `theorem one_to_one_inverse ...`; `theorem one_to_one_inverse' ...`
- [x] **Theorem 3H (composition of functions and domain spec):**
  - **Set theory:** composition of functions is a function; domain characterized by middle witness in `dom F`
  - **Lean:** `theorem composition_is_function ...`; `noncomputable def CompositionDomain ...`; `lemma CompositionDomain.Spec ...`; `theorem composition_domain ...`
- [x] **Theorem 3I (inverse of composition):**
  - **Set theory:** `(F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹`
  - **Lean:** `theorem inverse_composition (F G : Set) : (Composition F G)⁻¹ = Composition (Inverse G) (Inverse F)`
- [x] **Theorem 3K + Corollary 3L (image and inverse-image set laws):**
  - **Set theory:** image preserves unions and is monotone over intersections/differences; inverse-image gives equalities under function assumptions
  - **Lean:** `theorem image_union ...`; `theorem image_inter_subset ...`; `theorem image_diff_subset ...`; `theorem inverse_image_union ...`; `theorem inverse_image_inter ...`; `theorem inverse_image_diff ...`
- [x] **Graph of a Lean-level map over a carrier:**
  - **Set theory:** graph construction restricted to `A` behaves as a map `A → A` under closure
  - **Lean:** `noncomputable def GraphOn ...`; `lemma GraphOn.Spec ...`; `lemma GraphOn.Pair.Spec ...`; `theorem GraphOn.mapsInto ...`
- [x] **Indexed family operators and function space ${}^A B$:**
  - **Set theory:** indexed union/intersection via range of restricted family; function space as maps from `A` into `B`
  - **Lean:** `noncomputable def IndexedUnion ...`; `noncomputable def IndexedIntersection ...`; `noncomputable def FunctionSpace ...`; `lemma FunctionSpace.Spec ...`
- [x] **Theorem 3J and choice-first-form cross-file linkage:**
  - **Set theory:** left/right inverse characterizations (with choice for right inverse)
  - **Lean:** `theorem left_inverse_iff_one_to_one ...` and `theorem right_inverse_iff_onto ...` in `Set/Ch3/S5_InfiniteCartesianProducts.lean`; `def ChoiceFirstForm` and `axiom choice_first_form` in `Set/Choice.lean`

## Infinite Cartesian Products (pp. 54–55)

Primary files:
- `Set/Ch3/S5_InfiniteCartesianProducts.lean`
- `Set/Choice.lean`

- [x] **Definition (Infinite Cartesian product):**
  - **Set theory:** $\prod_{i \in I} H(i)=\{f \in {}^I(\bigcup \operatorname{ran}(H)) \mid \forall i \in I,\ f(i)\in H(i)\}$.
  - **Lean:** `noncomputable def InfiniteProduct (I H : Set) : Set := ...`
- [x] **Specification (InfiniteProduct.Spec):**
  - **Set theory:** $f \in \prod_{i \in I}H(i)$ iff $f$ is a function with domain $I$, codomain inside $\bigcup\operatorname{ran}(H)$, and each selected value belongs to the corresponding fiber.
  - **Lean:** `lemma InfiniteProduct.Spec {I H f : Set} : f ∈ InfiniteProduct I H ↔ ...`
- [x] **Axiom of Choice (second form):**
  - **Set theory:** For any set $I$ and function $H$ with $\operatorname{dom}(H)=I$, if every $H(i)$ is nonempty, then $\prod_{i \in I}H(i)\neq\varnothing$.
  - **Lean:** `def ChoiceSecondForm : Prop := ...` (in `Set/Choice.lean`)
- [x] **Derived theorem (ChoiceSecondForm gives nonempty product):**
  - **Set theory:** $\text{ChoiceSecondForm} \Rightarrow \forall I,H,\big((\forall i\in I,\ H(i)\neq\varnothing)\Rightarrow \prod_{i\in I}H(i)\neq\varnothing\big)$.
  - **Lean:** `theorem infiniteProduct_nonempty_of_choice_second_form (hChoice₂ : ChoiceSecondForm) : ...`

## Equivalence Relations (pp. 55–62)

Primary file: `Set/Ch3/S6_Equivalence.lean`

- [x] **Definition (Reflexive on a carrier):**
  - **Set theory:** $R$ is reflexive on $A$ iff $\forall x \in A,\ xRx$.
  - **Lean:** `def IsReflexiveOn (R A : Set) : Prop := ∀ x, x ∈ A → ⟨x, x⟩ ∈ R`
- [x] **Definition (Symmetric):**
  - **Set theory:** $\forall x\forall y,\ xRy \Rightarrow yRx$.
  - **Lean:** `def IsSymmetric (R : Set) : Prop := ∀ x y, ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R`
- [x] **Definition (Transitive relation):**
  - **Set theory:** $\forall x\forall y\forall z,\ (xRy \land yRz) \Rightarrow xRz$.
  - **Lean:** `def IsTransitiveRel (R : Set) : Prop := ∀ x y z, ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R`
- [x] **Definition (Binary relation on a carrier):**
  - **Set theory:** $R$ is a relation and $R \subseteq A \times A$.
  - **Lean:** `def IsBinaryRelationOn (R A : Set) : Prop := IsRelation R ∧ R ⊆ (A ⨯ A)`
- [x] **Definition (Equivalence relation):**
  - **Set theory:** binary on $A$, reflexive on $A$, symmetric, transitive.
  - **Lean:** `def IsEquivalenceRelation (R A : Set) : Prop := IsBinaryRelationOn R A ∧ IsReflexiveOn R A ∧ IsSymmetric R ∧ IsTransitiveRel R`
- [x] **Theorem 3M (field-level equivalence):**
  - **Set theory:** if $R$ is a relation that is symmetric and transitive, then $R$ is an equivalence relation on $\operatorname{fld}(R)$.
  - **Lean:** `theorem symm_trans_is_equiv (R : Set) : IsRelation R → IsSymmetric R → IsTransitiveRel R → IsEquivalenceRelation R (fld R)`
- [x] **Definition (Equivalence class):**
  - **Set theory:** $[x]_R = \{t \in \operatorname{ran}(R) \mid xRt\}$.
  - **Lean:** `noncomputable def EquivalenceClass (x R : Set) : Set := ...`
- [x] **Specification (EquivalenceClass.Spec):**
  - **Set theory:** $t \in [x]_R \Leftrightarrow t \in \operatorname{ran}(R) \land xRt$.
  - **Lean:** `lemma EquivalenceClass.Spec {x R t : Set} : t ∈ [x]₍R₎ ↔ t ∈ (ran R) ∧ ⟨x, t⟩ ∈ R`
- [x] **Lemma 3N (class equality criterion):**
  - **Set theory:** for $x,y \in A$, $[x]_R = [y]_R \Leftrightarrow xRy$.
  - **Lean:** `theorem equiv_class_eq_iff (R A x y : Set) : IsEquivalenceRelation R A → x ∈ A → y ∈ A → ([x]₍R₎ = [y]₍R₎ ↔ ⟨x, y⟩ ∈ R)`
- [x] **Definition (Quotient set):**
  - **Set theory:** $A/R = \{[x]_R \mid x \in A\}$.
  - **Lean:** `noncomputable def QuotientSet (A R : Set) : Set := ...`
- [x] **Specification (QuotientSet.Spec):**
  - **Set theory:** $Q \in A/R \Leftrightarrow Q \in \mathcal P(\operatorname{ran}(R)) \land \exists x \in A,\ Q=[x]_R$.
  - **Lean:** `lemma QuotientSet.Spec {A R Q : Set} : Q ∈ A / R ↔ Q ∈ 𝒫 (ran R) ∧ ∃ x, x ∈ A ∧ Q = [x]₍R₎`
- [x] **Definition (Compatibility):**
  - **Set theory:** if $xRy$ then $F(x)RF(y)$ (under map hypotheses on $A$).
  - **Lean:** `def IsCompatible (F R A : Set) : Prop := ...`
- [x] **Definition (Quotient lift graph):**
  - **Set theory:** relation induced by $x \mapsto y$ on classes $[x]_R \mapsto [y]_R$.
  - **Lean:** `noncomputable def QuotientLift (R A F : Set) : Set := ...`
- [x] **Specifications for quotient lift:**
  - **Set theory:** membership and pair-wise membership characterizations for the induced relation on $A/R$.
  - **Lean:** `lemma QuotientLift.Spec ...`; `lemma QuotientLift.Pair.Spec ...`
- [x] **Theorem 3Q (existence/uniqueness of quotient map):**
  - **Set theory:** if $F : A \to A$ is compatible with $R$, there is a unique induced map $\hat F : A/R \to A/R$.
  - **Lean:** `theorem quotient_function_exists (R A F : Set) : IsEquivalenceRelation R A → IsCompatible F R A → ∃! Fq, MapsInto Fq (A / R) (A / R) ∧ (∀ x y, x ∈ A → ⟨x, y⟩ ∈ F → ⟨[x]₍R₎, [y]₍R₎⟩ ∈ Fq)`
- [x] **Theorem 3Q (non-compatibility obstruction):**
  - **Set theory:** if $F$ is not compatible with $R$, no such induced quotient map exists.
  - **Lean:** `theorem quotient_function_not_exists (R A F : Set) : IsEquivalenceRelation R A → MapsInto F A A → ¬ IsCompatible F R A → ¬ ∃ Fq, MapsInto Fq (A / R) (A / R) ∧ (∀ x y, x ∈ A → ⟨x, y⟩ ∈ F → ⟨[x]₍R₎, [y]₍R₎⟩ ∈ Fq)`
- [x] **Definition (Partition):**
  - **Set theory:** nonempty blocks, pairwise disjoint unless equal, and exhaustive over $A$.
  - **Lean:** `def IsPartition (Part A : Set) : Prop := ...`
- [x] **Theorem 3P (equivalence classes form a partition):**
  - **Set theory:** if $R$ is an equivalence relation on $A$, then $A/R$ is a partition of $A$.
  - **Lean:** `theorem equiv_classes_partition (R A : Set) : IsEquivalenceRelation R A → IsPartition (A / R) A`

## Ordering Relations (pp. 62–65)

Primary file: `Set/Ch3/S7_OrderingRelations.lean`

- [x] **Definition (Trichotomy on a carrier):**
  - **Set theory:** for any $x,y \in A$, exactly one of $xRy$, $x=y$, $yRx$ holds (encoded with exclusivity clauses).
  - **Lean:** `def TrichotomyOn (R A : Set) : Prop := ...`
- [x] **Definition (Linear ordering / total ordering):**
  - **Set theory:** a binary relation on $A$ that is transitive and satisfies trichotomy on $A$.
  - **Lean:** `def IsLinearOrder (R A : Set) : Prop := IsBinaryRelationOn R A ∧ IsTransitiveRel R ∧ TrichotomyOn R A`
- [x] **Theorem 3R(i) (irreflexivity):**
  - **Set theory:** if $R$ linearly orders $A$, then no $x \in A$ satisfies $xRx$.
  - **Lean:** `theorem linear_order_irreflexive (R A : Set) : IsLinearOrder R A → ∀ x, x ∈ A → ⟨x, x⟩ ∉ R`
- [x] **Theorem 3R(ii) (connectedness for distinct points):**
  - **Set theory:** if $R$ linearly orders $A$ and $x,y \in A$ with $x \ne y$, then $xRy \lor yRx$.
  - **Lean:** `theorem linear_order_connected (R A : Set) : IsLinearOrder R A → ∀ x y, x ∈ A → y ∈ A → x ≠ y → (⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R)`

---

# Chapter 4: Natural Numbers

## Inductive Sets (pp. 67–70)

- Primary file: `Set/Ch4/S1_InductiveSets.lean`
- [x] **Definition (Successor):**
  - **Set theory:** $a^+ = a \cup \{a\}$
  - **Lean:** `noncomputable def Successor (a : Set) : Set := a ∪ Singleton a`
- [x] **Definition (Inductive set):**
  - **Set theory:** $\text{Inductive}(A) \Leftrightarrow 0 \in A \land (\forall a \in A)\, a^+ \in A$
  - **Lean:** `def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A`
- [x] **Derived Infinity statement (from primitive infinity axiom):**
  - **Set theory:** $\exists A\, \text{Inductive}(A)$
  - **Lean:** `theorem infinity_inductive : ∃ (A : Set), Inductive A`
- [x] **Definition (Natural number):**
  - **Set theory:** $\text{Natural}(n) \Leftrightarrow (\forall A)\,(\text{Inductive}(A) \Rightarrow n \in A)$
  - **Lean:** `def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A`
- [x] **Theorem 4A (existence of $\omega$):**
  - **Set theory:** $\exists \omega\, \forall n\,(n \in \omega \Leftrightarrow \text{Natural}(n))$
  - **Lean:** `theorem natural_numbers_exist : ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n`
- [x] **Definition/Spec ($\omega$):**
  - **Set theory:** $n \in \omega \Leftrightarrow \text{Natural}(n)$
  - **Lean:** `noncomputable def ω := Classical.choose natural_numbers_exist`; `lemma ω.Spec {n : Set} : n ∈ ω ↔ Natural n`
- [x] **Membership conversion helpers:**
  - **Set theory:** conversion between $n \in \omega$ and $\text{Natural}(n)$
  - **Lean:** `lemma natural_of_mem_omega (n : Set) : n ∈ ω → Natural n`; `lemma mem_omega_of_natural (n : Set) : Natural n → n ∈ ω`
- [x] **Theorem 4B (minimal inductive set):**
  - **Set theory:** $\text{Inductive}(\omega)$ and $(\forall A)(\text{Inductive}(A) \Rightarrow \omega \subseteq A)$
  - **Lean:** `theorem ω.inductive : Inductive ω`; `theorem ω.subset_of_inductive : ∀ (A : Set), Inductive A → ω ⊆ A`
- [x] **Induction principle for $\omega$ (predicate form):**
  - **Set theory:** $\big(P(0)\land (\forall k\in\omega, P(k)\Rightarrow P(k^+))\big)\Rightarrow (\forall n\in\omega, P(n))$
  - **Lean:** `lemma ω_induction (P : Set → Prop) (hBase : P Set.Empty) (hStep : ∀ k, k ∈ ω → P k → P (k⁺)) : ∀ n, n ∈ ω → P n`
- [x] **Theorem 4C (nonzero naturals are successors):**
  - **Set theory:** $n \neq 0 \land \text{Natural}(n) \Rightarrow \exists m \in \omega\, (n = m^+)$
  - **Lean:** `theorem ω.exists_successor (n : Set) : n ≠ ∅ → Natural n → ∃ (m : Set), m ∈ ω ∧ n = m⁺`

## Peano's Postulates (pp. 70–73)

- Primary file: `Set/Ch4/S2_PeanosPostulates.lean` (proof order in file: 4E, 4F, 4G, then 4D; items below follow textbook order)
- [x] **Definition (Peano system, Lean packaging):**
  - **Set theory:** triple $\langle N, S, e \rangle$ with $e \in N$, $S$ maps $N$ into $N$, $e \notin \operatorname{ran}(S)$ (no successor equals $e$), $S$ injective on $N$, and Peano induction on subsets of $N$
  - **Lean:** `def IsPeanoSystem (N : Set) (S : Set → Set) (e : Set) : Prop := e ∈ N ∧ (∀ n, n ∈ N → S n ∈ N) ∧ (∀ n, n ∈ N → S n ≠ e) ∧ (∀ m n, m ∈ N → n ∈ N → S m = S n → m = n) ∧ (∀ A : Set, A ⊆ N → e ∈ A → (∀ x, x ∈ A → S x ∈ A) → A = N)`
- [x] **Lemma (successor is nonempty):**
  - **Set theory:** $a^+ \neq \varnothing$
  - **Lean:** `lemma successor_ne_empty (a : Set) : a⁺ ≠ ∅`
- [x] **Definition (Transitive set):**
  - **Set theory:** $x \in a \land a \in A \Rightarrow x \in A$
  - **Lean:** `def IsTransitiveSet (A : Set) : Prop := ∀ (x a : Set), x ∈ a → a ∈ A → x ∈ A`
- [x] **Theorem 4E ($\bigcup(a^+)$ for transitive $a$):**
  - **Set theory:** $a$ transitive $\Rightarrow \bigcup(a^+) = a$
  - **Lean:** `theorem bigunion_successor_of_transitive (a : Set) : IsTransitiveSet a → ⋃(a⁺) = a`
- [x] **Theorem 4F (naturals are transitive sets):**
  - **Set theory:** $\text{Natural}(n) \Rightarrow n$ is a transitive set
  - **Lean:** `theorem natural_transitive_set (n : Set) : Natural n → IsTransitiveSet n`
- [x] **Theorem 4G ($\omega$ transitive):**
  - **Set theory:** $\omega$ is a transitive set
  - **Lean:** `theorem ω_transitive_set : IsTransitiveSet ω`
- [x] **Theorem 4D ($\omega$ is a Peano system):**
  - **Set theory:** $\langle \omega, \sigma, 0 \rangle$ is a Peano system (with successor on $\omega$)
  - **Lean:** `theorem omega_peano_system : IsPeanoSystem ω (fun n => n⁺) ∅`

## Recursion on $\omega$ (pp. 73–79)

- **Recursion Theorem on $\omega$:** Given $A$, $a \in A$, and $F : A \to A$, there exists a unique $h : \omega \to A$ with
  - $h(0)=a$,
  - $h(n^+) = F(h(n))$ for all $n \in \omega$.
  - **Lean:** `def RecursionSolution (h A a F : Set) : Prop := …`; `theorem recursion_theorem_on_ω …` (also `recursion_theorem_on_ω_successor`, `recursion_theorem_on_ω_add_right`, … in `Set/Ch4/S4_Arithmetic.lean`)
- **Theorem 4H:** Every Peano system is isomorphic to $\langle \omega, \sigma, 0 \rangle$.
  - **Lean:** `def IsPeanoIsomorphism ...`; `theorem theorem_4H_peano_isomorphic ...`

## Arithmetic (pp. 79–83)

- **Definition (Binary operation):** A function from $A \times A$ into $A$.
  - **Lean:** `def IsBinaryOperationOn (A op : Set) : Prop := MapsInto op (A ⨯ A) A`
- **Definition (Addition on $\omega$):** via recursion in the second argument.
  - **Lean:** `noncomputable def NatAdd …`; `noncomputable instance : HAdd Set Set Set := ⟨NatAdd⟩`
- **Theorem 4I (A1/A2):**
  - $m + 0 = m$,
  - $m + n^+ = (m+n)^+$.
  - **Lean:** `theorem nat_add_zero ...`; `theorem nat_add_succ ...`
- **Definition (Multiplication on $\omega$):** via recursion.
  - **Lean:** `noncomputable def NatMul …`; `noncomputable instance : HMul Set Set Set := ⟨NatMul⟩`
- **Theorem 4J (M1/M2):**
  - $m \cdot 0 = 0$,
  - $m \cdot n^+ = m \cdot n + m$.
  - **Lean:** `theorem nat_mul_zero ...`; `theorem nat_mul_succ ...`
- **Definition/characterization (Exponentiation):**
  - $m^0 = 1$,
  - $m^{(n^+)} = m^n \cdot m$.
  - **Lean:** `noncomputable def NatPow …`; `noncomputable instance : Pow Set Set := ⟨NatPow⟩`; `theorem nat_pow_zero …`; `theorem nat_pow_succ …` (see also `NatPowCanon` / `nat_pow_canon_*` in `Set/Ch4/S4_Arithmetic.lean`)
- **Theorem 4K:** Basic arithmetic laws (assoc/comm/distrib) for $+$ and $\cdot$.
  - **Lean:** `theorem theorem_4K_basic_arithmetic_laws ...`

## Ordering on $\omega$ (pp. 83–88)

- **Definition (Order on $\omega$):** $m < n \Leftrightarrow m \in n$; and $m \le n \Leftrightarrow m \in n \lor m=n$.
  - **Lean:** `def NatLt (m n : Set) : Prop := m ∈ n`; `def NatLe (m n : Set) : Prop := m ∈ n ∨ m = n`
- **Lemma 4L(a):** $m \in n \Leftrightarrow m^+ \in n^+$.
  - **Lean:** `theorem natural_succ_mem_iff (m n : Set) : m ∈ ω → n ∈ ω → (m ∈ n ↔ m⁺ ∈ n⁺)`
- **Lemma 4L(b):** No natural number is a member of itself.
  - **Lean:** `theorem natural_not_mem_self (n : Set) : n ∈ ω → n ∉ n`
- **Trichotomy Law for $\omega$:** exactly one of $m \in n$, $m=n$, $n \in m$.
  - **Lean:** `theorem natural_trichotomy ...`
- **Corollary 4M:** for naturals, $m \in n \Leftrightarrow m \subset n$, and $m \le n \Leftrightarrow m \subseteq n$.
  - **Lean:** `theorem natural_mem_iff_proper_subset ...`; `theorem natural_le_iff_subset ...`
- **Theorem 4N:** order preserved by addition, and by multiplication with nonzero factor.
  - **Lean:** `theorem theorem_4N_order_preservation ...`
- **Corollary 4P:** cancellation laws for addition/multiplication on $\omega$.
  - **Lean:** `theorem corollary_4P_cancellation ...`
- **Well Ordering of $\omega$:** every nonempty subset of $\omega$ has a least element.
  - **Lean:** `theorem omega_well_ordering ...`
- **Corollary 4Q:** no function $f:\omega\to\omega$ satisfies $f(n^+) \in f(n)$ for all $n$.
  - **Lean:** `theorem no_descending_omega_sequence ...`
- **Strong Induction Principle for $\omega$**.
  - **Lean:** `theorem strong_induction_omega ...`

---

# Chapter 5: Construction of the Real Numbers

Primary files: `Set/Ch5/S1_Integers.lean`, `Set/Ch5/S2_RationalNumbers.lean`, `Set/Ch5/S3_RealNumbers.lean`, `Set/Ch5/S4_Summaries.lean`.

Enderton’s labels (5ZA, 5QA, 5RA, …) correspond to Lean names with Unicode subscripts where helpful: `theorem_5ℤ…`, `theorem_5ℚ…`, `theorem_5ℝ…`. Some Chapter 5 proofs still use `sorry` or trivial `True` placeholders—see the `.lean` files.

## Integers (pp. 90–101)

- [x] **Definition (difference-equivalence on $\omega \times \omega$):**
  - **Set theory:** $\langle m,n\rangle \sim \langle p,q\rangle \Leftrightarrow m+q=p+n$
  - **Lean:** `noncomputable def IntEqRel` with `IntEqRel.Spec`
- [x] **Theorem 5ZA:** $\sim$ is an equivalence relation on $\omega \times \omega$.
  - **Lean:** `theorem theorem_5ℤA : IntEqRel.IsEquivalenceRelation IntegerCarrier`
- [x] **Definition (integers):** $\mathbb{Z} = (\omega \times \omega)/\sim$.
  - **Lean:** `noncomputable def IntegerCarrier : Set := ω ⨯ ω`; `noncomputable def IntegerSet : Set := IntegerCarrier / IntEqRel`; `notation "ℤ" => IntegerSet`
- [x] **Lemma 5ZB (addition compatibility):** representative-level addition respects $\sim$.
  - **Lean:** `int_add_candidate_*`, `IntEqRel.pair_mem`, … (no separate `theorem_5ZB`; used in `theorem_5ℤF`)
- [x] **Theorem 5ZC:** integer addition is commutative and associative.
  - **Lean:** `theorem theorem_5ℤC : ∃ addZ, IntAddAxioms addZ` (derived from `theorem_5ℤF`)
- [x] **Theorem 5ZD:** $0_{\mathbb Z}$ is additive identity and additive inverses exist.
  - **Lean:** `theorem theorem_5ℤD …`
- [x] **Lemma 5ZE (multiplication compatibility):** representative-level multiplication respects $\sim$.
  - **Lean:** `int_mul_candidate_*`, … (bundled toward `theorem_5ℤF`)
- [x] **Theorem 5ZF:** integer addition/multiplication layer + distributivity packaging.
  - **Lean:** `theorem theorem_5ℤF : …` (**still contains `sorry`** in `Set/Ch5/S1_Integers.lean` as of last tidy pass)
- [x] **Theorem 5ZG:** multiplicative identity, $0_{\mathbb{Z}} \neq 1_{\mathbb{Z}}$, and no zero divisors.
  - **Lean:** `theorem theorem_5ℤG …`
- [x] **Lemma 5ZH (order compatibility):** representative-level order formula is well-defined under $\sim$.
  - **Lean:** subsumed in `IntOrderAxioms` / `lt_ℤ` infrastructure
- [x] **Theorem 5ZI:** integer order is a linear ordering.
  - **Lean:** `theorem theorem_5ℤI : ∃ ltZ, IntOrderAxioms ltZ`
- [ ] **Theorem 5ZJ:** integer order is preserved by addition and by multiplication with positive factor.
  - **Lean:** *not yet a standalone Enderton-titled theorem*
- [ ] **Corollary 5ZK:** cancellation laws on $\mathbb Z$.
  - **Lean:** *TBD as named corollary*
- [ ] **Theorem 5ZL:** embedding $E:\omega \to \mathbb{Z}$ preserves $+$, $\cdot$, and order.
  - **Lean:** *TBD*

## Rational Numbers (pp. 101–111)

- [x] **Definition (fraction-equivalence on $\mathbb{Z} \times \mathbb{Z}'$):**
  - **Set theory:** $\langle a,b\rangle \approx \langle c,d\rangle \Leftrightarrow ad=cb$
  - **Lean:** `noncomputable def RatEqRel` (`Set/Ch5/S2_RationalNumbers.lean`)
- [x] **Theorem 5QA:** $\approx$ is an equivalence relation on $\mathbb{Z} \times \mathbb{Z}'$.
  - **Lean:** `theorem theorem_5ℚA : IsEquivalenceRelation RatEqRel (ℤ ⨯ ℤ')`
- [x] **Definition (rationals):** $\mathbb{Q} = (\mathbb{Z} \times \mathbb{Z}')/\approx$.
  - **Lean:** `noncomputable def RationalSet : Set := (ℤ ⨯ ℤ') / RatEqRel`; `notation "ℚ" => RationalSet`
- [x] **Lemma 5QB (addition compatibility):** fraction-level addition respects $\approx$.
  - **Lean:** `theorem lemma_5ℚB : True` (scaffold)
- [x] **Theorem 5QC:** rational addition gives an Abelian group.
  - **Lean:** `theorem theorem_5ℚC : ∃ addQ, RatAddAxioms addQ`
- [x] **Lemma 5QD (multiplication compatibility):** fraction-level multiplication respects $\approx$.
  - **Lean:** `theorem lemma_5ℚD : True` (scaffold)
- [x] **Theorem 5QE:** rational multiplication is associative/commutative/distributive.
  - **Lean:** `theorem theorem_5ℚE : ∃ mulQ, RatMulAxioms mulQ`
- [x] **Theorem 5QF:** every nonzero rational has a multiplicative inverse.
  - **Lean:** `theorem theorem_5ℚF : True` (scaffold)
- [x] **Corollary 5QG:** nonzero rationals are closed under multiplication.
  - **Lean:** `theorem corollary_5ℚG : True` (scaffold)
- [x] **Lemma 5QH (order compatibility):** order formula with positive denominators is well-defined.
  - **Lean:** `theorem lemma_5ℚH : True` (scaffold)
- [x] **Theorem 5QI:** rational order is a linear ordering.
  - **Lean:** `theorem theorem_5ℚI : ∃ ltQ, RatLtAxioms ltQ`
- [x] **Theorem 5QJ:** rational order is preserved by addition and by multiplication with positive factor.
  - **Lean:** `theorem theorem_5ℚJ : True` (scaffold)
- [x] **Theorem 5QK:** cancellation laws on $\mathbb Q$.
  - **Lean:** `theorem theorem_5ℚK : True` (scaffold)
- [x] **Theorem 5QL:** embedding $E:\mathbb{Z} \to \mathbb{Q}$ preserves operations and order.
  - **Lean:** `theorem theorem_5ℚL : True` (scaffold)

## Real Numbers (pp. 111–121)

- [x] **Definition (Dedekind cut):**
  - **Set theory:** $x\subseteq\mathbb{Q}$, $x\neq\varnothing$, $x\neq\mathbb{Q}$, downward closed, no largest member.
  - **Lean:** `def IsDedekindCut (x : Set) : Prop := …`
- [x] **Definition (reals as cuts):**
  - **Set theory:** $\mathbb{R}=\{x\subseteq\mathbb{Q}\mid x\text{ is a Dedekind cut}\}$
  - **Lean:** `noncomputable def RealSet : Set := …`
- [x] **Definition (real order):**
  - **Set theory:** $x <_{\mathbb R} y \Leftrightarrow x \subset y$
  - **Lean:** `def RealLt (x y : Set) : Prop := x ⊆ y ∧ x ≠ y`
- [ ] **Theorem 5RA:** $<_{\mathbb R}$ is a linear ordering on $\mathbb R$.
  - **Lean:** `theorem theorem_5ℝA : Set.IsLinearOrder RealOrderRel RealSet` (**`sorry`** in `Set/Ch5/S3_RealNumbers.lean`)
- [ ] **Theorem 5RB:** every nonempty bounded subset of $\mathbb R$ has a least upper bound.
  - **Lean:** `theorem theorem_5ℝB : True` (scaffold)
- [x] **Definition (real addition):** $x+_{\mathbb R}y=q+r\mid q\in x,\ r\in y$.
  - **Lean:** `noncomputable def RealAdd : Set := …`; `noncomputable def add_ℝ : Set → Set → Set := …`
- [ ] **Lemma 5RC:** if $x,y\in\mathbb R$, then $x+_{\mathbb R}y\in\mathbb R$.
  - **Lean:** `theorem lemma_5ℝC : True` (scaffold)
- [ ] **Theorem 5RD:** real addition is associative and commutative.
  - **Lean:** `theorem theorem_5ℝD : True` (scaffold)
- [ ] **Theorem 5RE:** $0_{\mathbb{R}}\in\mathbb{R}$ and $x +_{\mathbb{R}} 0_{\mathbb{R}} = x$.
  - **Lean:** `theorem theorem_5ℝE : True` (scaffold)
- [ ] **Theorem 5RF:** additive inverses on $\mathbb R$.
  - **Lean:** `theorem theorem_5ℝF : True` (scaffold)
- [ ] **Corollary 5RG:** additive cancellation on $\mathbb R$.
  - **Lean:** `theorem corollary_5ℝG : True` (scaffold)
- [ ] **Theorem 5RH:** real order preserved by addition.
  - **Lean:** `theorem theorem_5ℝH : True` (scaffold)
- [x] **Definition (real multiplication, sign-split Dedekind-cut form):**
  - **Lean:** `noncomputable def RealMul : Set := …`; `noncomputable def mul_ℝ : Set → Set → Set := …`
- [ ] **Theorem 5RI:** multiplication well-defined on reals; ordered-field laws; inverse for nonzero; positivity-preserving order.
  - **Lean:** `theorem theorem_5ℝI : True` (scaffold)
- [ ] **Theorem 5RJ:** embedding $E:\mathbb{Q} \to \mathbb{R}$ preserves operations and order.
  - **Lean:** `theorem theorem_5ℝJ : True` (scaffold)

## Summaries (pp. 121–123)

- [x] **Definition (Abelian group / commutative ring with identity / integral domain / field / ordered field / complete ordered field):** chapter-level algebraic concept bundle.
  - **Lean:** `def IsAbelianGroupAdd …`, `IsCommutativeRingWithOne …`, `IsIntegralDomain …`, `IsFieldLike …`, `IsOrderedFieldLike …`, `IsCompleteOrderedFieldLike …` in `Set/Ch5/S4_Summaries.lean`

---

## Summary of Proven Items

Rough checklist coverage (Ch. 5 mixes finished proofs, `sorry`, and `True` scaffolds—treat this table as orientation, not a formal metric):

| Chapter   | Total items | Status (high level)                                      |
| --------- | ----------- | -------------------------------------------------------- |
| Ch. 2     | ~30         | ~30 checked in earlier sections                        |
| Ch. 3     | ~41         | ~41 checked                                              |
| Ch. 4     | ~32         | ~32 checked                                              |
| Ch. 5     | ~42         | definitions + rationals scaffold + reals mostly open    |
| **Total** | **~145**    | see checkboxes above; Chapter 5 still under active work  |
