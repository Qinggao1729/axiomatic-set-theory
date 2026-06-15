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

## Repository Refactor Backlog

- [ ] **Numbered declaration naming migration (deferred):**
  - **Set theory:** Keep theorem statements fixed first; perform global naming rewrite only after statement-level audit is complete.
  - **Lean:** Adopt short numbered prefixes (`thm_`, `lem_`, `cor_`, `ax_`) for explicitly numbered Enderton results, then do a repo-wide rewrite and remove temporary compatibility aliases.
- [ ] **Proof-style + notation normalization pass (repo-wide, staged):**
  - **Set theory:** Ensure proofs use the project's defined notations consistently and prefer simpler, readable derivations over redundant proof plumbing.
  - **Lean:** Audit each chapter file against `proof_style.md` (notation usage, simplified `exact`/`simp` patterns, avoiding unnecessary `have`/`by exact` wrappers), then run `lake build` after each stage.

# Chapter 2: Axioms and Operations

## Section 1 (pp. 17–23): Core Axioms + Binary/Subset Operations

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
  - **Lean:** `lemma Singleton.Spec {x y : Set} : y ∈ Singleton x ↔ y = x`

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
  - **Lean:** `theorem thm_2A_no_universal_set : ¬ ∃ (A : Set), ∀ (x : Set), x ∈ A`

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
  - **Lean:** `theorem thm_2B_intersection (A : Set) (h : A.Nonempty) : ∃! (B : Set), ∀ (x : Set), x ∈ B ↔ (∀ (a : Set), a ∈ A → x ∈ a)`

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
  - **Lean:** `lemma FamilyUnion.Spec {A ℬ t : Set} : t ∈ FamilyUnion A ℬ ↔ t ∈ 𝒫 (A ∪ ⋃ℬ) ∧ ∃ X : Set, X ∈ ℬ ∧ t = A ∪ X`
- [x] **Nonempty (FamilyUnion):**
  - **Set theory:** $\mathscr{B}\neq\varnothing \Rightarrow \{A \cup X \mid X \in \mathscr{B}\}\neq\varnothing$
  - **Lean:** `theorem FamilyUnion.nonempty (A ℬ : Set) (hℬ : ℬ.Nonempty) : (FamilyUnion A ℬ).Nonempty`
- [x] **Definition (FamilyInter):**
  - **Set theory:** $\{A \cap X \mid X \in \mathscr{B}\}$
  - **Lean:** `noncomputable def FamilyInter (A ℬ : Set) : Set := ...`
- [x] **Specification (FamilyInter.Spec):**
  - **Set theory:** $t \in \{A \cap X \mid X \in \mathscr{B}\} \Leftrightarrow t \in \mathcal{P}(A) \land \exists X(X \in \mathscr{B} \land t = A \cap X)$
  - **Lean:** `lemma FamilyInter.Spec {A ℬ t : Set} : t ∈ FamilyInter A ℬ ↔ t ∈ 𝒫 A ∧ ∃ X : Set, X ∈ ℬ ∧ t = A ∩ X`
- [x] **Definition (FamilyDiff):**
  - **Set theory:** $\{C - X \mid X \in \mathscr{A}\}$
  - **Lean:** `noncomputable def FamilyDiff (C 𝒜 : Set) : Set := ...`
- [x] **Specification (FamilyDiff.Spec):**
  - **Set theory:** $t \in \{C - X \mid X \in \mathscr{A}\} \Leftrightarrow t \in \mathcal{P}(C) \land \exists X(X \in \mathscr{A} \land t = C - X)$
  - **Lean:** `lemma FamilyDiff.Spec {C 𝒜 t : Set} : t ∈ FamilyDiff C 𝒜 ↔ t ∈ 𝒫 C ∧ ∃ X : Set, X ∈ 𝒜 ∧ t = C - X`
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

## Ordered Pairs (pp. 35–39)

Primary file: `Set/Ch3/S1_OrderedPairs.lean`
Note: internal helper lemmas are intentionally omitted from this checklist.

- [x] **Definition (Ordered pair):**
  - **Set theory:** $\langle x, y \rangle = \{x,\{x, y\}\}$
  - **Lean:** `noncomputable def OrderedPair (x y : Set) : Set := Pair (Singleton x) (Pair x y)`
- [x] **Specification (OrderedPair.Spec):**
  - **Set theory:** $\forall w\,(w \in \langle x, y\rangle \Leftrightarrow w = \{x\} \lor w = \{x,y\})$
  - **Lean:** `lemma OrderedPair.Spec {x y w : Set} : w ∈ OrderedPair x y ↔ w = Singleton x ∨ w = Pair x y`
- [x] **Notation (preferred ordered pair syntax):**
  - **Set theory:** Use $\langle x, y \rangle$ as textbook notation.
  - **Lean:** `notation:90 "⟪" x ", " y "⟫" => OrderedPair x y`
- [x] **Theorem 3A (uniqueness):**
  - **Set theory:** $\langle u, v \rangle = \langle x, y \rangle \Leftrightarrow (u = x \land v = y)$
  - **Lean:** `theorem thm_3A_ordered_pair_uniqueness (u v x y : Set) : ⟪u, v⟫ = ⟪x, y⟫ ↔ u = x ∧ v = y`
- [x] **Lemma 3B:**
  - **Set theory:** $x \in C \land y \in C \Rightarrow \langle x, y \rangle \in \mathcal{P}\mathcal{P}C$
  - **Lean:** `lemma lem_3B_ordered_pair_in_power_power (x y C : Set) : x ∈ C → y ∈ C → OrderedPair x y ∈ Power (Power C)`
- [x] **Corollary 3C (existence of product carrier):**
  - **Set theory:** $\exists C\,\forall w\,(w \in C \Leftrightarrow w \in \mathcal{P}\mathcal{P}(A \cup B) \land \exists x\exists y\,(x \in A \land y \in B \land w=\langle x,y\rangle))$
  - **Lean:** `lemma OrderedPair.product (A B : Set) : ∃ C, ∀ w, w ∈ C ↔ w ∈ 𝒫 𝒫 (A ∪ B) ∧ ∃ x y, x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫`
- [x] **Definition (Cartesian product):**
  - **Set theory:** $A \times B = \{\langle x, y\rangle \mid x \in A \land y \in B\}$
  - **Lean:** `noncomputable def Product (A B : Set) : Set := Classical.choose (OrderedPair.product A B)`
- [x] **Specification (Product.Spec):**
  - **Set theory:** $\forall w\,(w \in A \times B \Leftrightarrow \exists x\exists y\,(x \in A \land y \in B \land w=\langle x,y\rangle))$
  - **Lean:** `lemma Product.Spec {A B w : Set} : w ∈ Product A B ↔ ∃ x y, x ∈ A ∧ y ∈ B ∧ w = ⟪x, y⟫`

## Relations (pp. 39–41)

Primary file: `Set/Ch3/S2_Relations.lean`

- [x] **Lemma 3D:**
  - **Set theory:** $\langle x, y \rangle \in A \Rightarrow x \in \bigcup\bigcup A \land y \in \bigcup\bigcup A$
  - **Lean:** `lemma lem_3D_ordered_pair_in_union_union (x y A : Set) : ⟪x, y⟫ ∈ A → x ∈ ⋃⋃A ∧ y ∈ ⋃⋃A`
- [x] **Definition (Relation):**
  - **Set theory:** $R$ is a relation iff $\forall w \in R\exists x\exists y(w = \langle x, y \rangle)$
  - **Lean:** `def IsRelation (R : Set) : Prop := ∀ w, w ∈ R → ∃ x y, w = ⟪x, y⟫`
- [x] **Definition (Domain):**
  - **Set theory:** $\operatorname{dom}(R)=\{x \mid \exists y\,\langle x,y\rangle\in R\}$
  - **Lean:** `noncomputable def Domain (R : Set) : Set := ...`
- [x] **Specification (Domain.Spec):**
  - **Set theory:** $x \in \operatorname{dom}(R) \Leftrightarrow \exists y\,\langle x,y\rangle\in R$
  - **Lean:** `lemma Domain.Spec {R x : Set} : x ∈ Domain R ↔ ∃ y, ⟪x, y⟫ ∈ R`
- [x] **Notation (Domain):**
  - **Set theory:** $\operatorname{dom}(R)$
  - **Lean:** `notation:90 "dom " R => Domain R`
- [x] **Definition (Range):**
  - **Set theory:** $\operatorname{ran}(R)=\{y \mid \exists x\,\langle x,y\rangle\in R\}$
  - **Lean:** `noncomputable def Range (R : Set) : Set := ...`
- [x] **Specification (Range.Spec):**
  - **Set theory:** $y \in \operatorname{ran}(R) \Leftrightarrow \exists x\,\langle x,y\rangle\in R$
  - **Lean:** `lemma Range.Spec {R y : Set} : y ∈ Range R ↔ ∃ x, ⟪x, y⟫ ∈ R`
- [x] **Notation (Range):**
  - **Set theory:** $\operatorname{ran}(R)$
  - **Lean:** `notation:90 "ran " R => Range R`
- [x] **Definition (Field):**
  - **Set theory:** $\operatorname{fld}(R)=\operatorname{dom}(R)\cup\operatorname{ran}(R)$
  - **Lean:** `noncomputable def Field (R : Set) : Set := (dom R) ∪ (ran R)`
- [x] **Specification (Field.Spec):**
  - **Set theory:** $z\in \operatorname{fld}(R)\Leftrightarrow z\in\operatorname{dom}(R)\lor z\in\operatorname{ran}(R)$
  - **Lean:** `lemma Field.Spec {R z : Set} : z ∈ Field R ↔ z ∈ (dom R) ∨ z ∈ (ran R)`
- [x] **Notation (Field):**
  - **Set theory:** $\operatorname{fld}(R)$
  - **Lean:** `notation:90 "fld " R => Field R`
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

_Checklist audit policy (manual): items through **`Set/Ch3/S4_Functions.lean`** and **`Set/Ch4/S1_InductiveSets.lean`** are treated as reviewed against Lean. Later sections remain unchecked until explicitly re-verified._

## Functions (pp. 42–54)

Primary files:
- `Set/Ch3/S4_Functions.lean` — AC-free core (3E–3I, 3K, 3L, indexed families, function space) **plus** Theorem 3J(a)/(b) at the bottom inside a reopened `namespace Choice`
- `Set/Choice.lean` — shared AC infrastructure and non-local forms (with predicates inlined to break the import cycle into `S4_Functions`)

- [x] **Definition (Function):**
  - **Set theory:** $F$ is a relation and for each $x \in \operatorname{dom}(F)$ there exists a unique $y$ with $\langle x, y \rangle \in F$
  - **Lean:** `def IsFunction (F : Set) : Prop := IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟪x, y⟫ ∈ F`
- [x] **Definition (Maps into):**
  - **Set theory:** $F : A \to B$ iff `IsFunction F`, `dom F = A`, and `ran F ⊆ B`
  - **Lean:** `def MapsInto (F A B : Set) : Prop := IsFunction F ∧ (dom F) = A ∧ (ran F) ⊆ B`
- [x] **Definition (Maps onto):**
  - **Set theory:** $F$ maps $A$ onto $B$ iff $F : A \to B$ and `ran F = B`
  - **Lean:** `def MapsOnto (F A B : Set) : Prop := MapsInto F A B ∧ (ran F) = B`
- [x] **Definition (Single-rooted / one-to-one wrapper):**
  - **Set theory:** single-rooted means uniqueness of preimage for each element of the range
  - **Lean:** `def IsSingleRooted (R : Set) : Prop := ∀ (y : Set), y ∈ (ran R) → ∃! (x : Set), ⟪x, y⟫ ∈ R`; `def IsOneToOne (F : Set) : Prop := IsFunction F ∧ IsSingleRooted F`
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
  - **Lean:** `lemma Relation.Pair.mem_dom ...`; `lemma Relation.Pair.mem_ran ...`; `lemma Product.Pair.Spec ...`; `lemma function_value_unique ...`
- [x] **Theorem 3E (inverse swaps domain/range, double inverse):**
  - **Set theory:** `dom(F⁻¹)=ran(F)`, `ran(F⁻¹)=dom(F)`, and for relations `(F⁻¹)⁻¹=F`
  - **Lean:** `theorem thm_3E_domain_inverse ...`; `theorem thm_3E_range_inverse ...`; `theorem thm_3E_relation_inverse_inverse ...`
- [x] **Theorem 3F (function vs single-rooted under inverse):**
  - **Set theory:** `IsFunction (F⁻¹) ↔ IsSingleRooted F`, and for relations `IsFunction F ↔ IsSingleRooted (F⁻¹)`
  - **Lean:** `theorem thm_3F_inverse_single_rooted ...`; `theorem thm_3F_relation_function_single_rooted ...`
- [x] **Theorem 3G (inverse evaluation laws for one-to-one functions):**
  - **Set theory:** if `F` is one-to-one, inverse evaluation composes back to the original element
  - **Lean:** `theorem thm_3G_one_to_one_inverse ...`; `theorem thm_3G_one_to_one_inverse_ran ...`
- [x] **Theorem 3H (composition of functions and domain spec):**
  - **Set theory:** composition of functions is a function; domain characterized by middle witness in `dom F`
  - **Lean:** `theorem thm_3H_composition_is_function ...`; `noncomputable def CompositionDomain ...`; `lemma CompositionDomain.Spec ...`; `theorem thm_3H_composition_domain ...`
- [x] **Theorem 3I (inverse of composition):**
  - **Set theory:** `(F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹`
  - **Lean:** `theorem thm_3I_inverse_composition (F G : Set) : (Composition F G)⁻¹ = Composition (Inverse G) (Inverse F)`
- [x] **Image family (auxiliary set for arbitrary 3K/3L forms):**
  - **Set theory:** the set `{F[A] | A ∈ 𝒜}` used in the second halves of Theorem 3K(a)(b) and in Corollary 3L
  - **Lean:** `noncomputable def ImageFamily (F 𝒜 : Set) : Set`; `lemma ImageFamily.Spec ...`; `lemma ImageFamily.Nonempty ...`
- [x] **Theorem 3K(a) (image of a union):**
  - **Set theory:** `F[A ∪ B] = F[A] ∪ F[B]` and `F[⋃𝒜] = ⋃{F[A] | A ∈ 𝒜}` (for any `F`)
  - **Lean:** `theorem thm_3Ka_image_union ...`; `theorem thm_3Ka_image_bigUnion ...`
- [x] **Theorem 3K(b) (image of an intersection):**
  - **Set theory:** `F[A ∩ B] ⊆ F[A] ∩ F[B]` and `F[⋂𝒜] ⊆ ⋂{F[A] | A ∈ 𝒜}` (for nonempty `𝒜`); equality if `F` is single-rooted
  - **Lean:** `theorem thm_3Kb_image_inter_subset ...`; `theorem thm_3Kb_image_bigInter_subset ...`; `theorem thm_3Kb_image_inter_eq_of_single_rooted ...`; `theorem thm_3Kb_image_bigInter_eq_of_single_rooted ...`
- [x] **Theorem 3K(c) (image of a difference):**
  - **Set theory:** `F[A] - F[B] ⊆ F[A - B]`; equality if `F` is single-rooted
  - **Lean:** `theorem thm_3Kc_image_diff_subset ...`; `theorem thm_3Kc_image_diff_eq_of_single_rooted ...`
- [x] **Corollary 3L (inverse image is well-behaved):**
  - **Set theory:** for any function `G`: `G⁻¹[⋃𝒜] = ⋃{G⁻¹[A] | A ∈ 𝒜}`, `G⁻¹[⋂𝒜] = ⋂{G⁻¹[A] | A ∈ 𝒜}` (for nonempty `𝒜`), and `G⁻¹[A - B] = G⁻¹[A] - G⁻¹[B]`
  - **Lean:** `theorem cor_3La_inverse_image_bigUnion ...`; `theorem cor_3Lb_inverse_image_bigInter ...`; `theorem cor_3Lc_inverse_image_diff ...`
- [x] **Binary inverse-image corollaries (not in 3L proper, kept as convenience):**
  - **Set theory:** binary forms `G⁻¹[A ∪ B] = G⁻¹[A] ∪ G⁻¹[B]` and `G⁻¹[A ∩ B] = G⁻¹[A] ∩ G⁻¹[B]` (the latter for `G` a function)
  - **Lean:** `theorem inverse_image_union ...`; `theorem inverse_image_inter ...`
- [x] **Graph of a Lean-level map over a carrier (not Enderton; Ch4 scaffolding):**
  - **Set theory:** graph construction restricted to `A` behaves as a map `A → A` under closure
  - **Lean:** `noncomputable def GraphOn ...`; `lemma GraphOn.Spec ...`; `lemma GraphOn.Pair.Spec ...`; `theorem GraphOn.mapsInto ...` — moved to the top of `Set/Ch4/S3_RecursionOnOmega.lean` since this construction only supports the recursion / Peano isomorphism / arithmetic recurrences in Chapter 4.
- [x] **Indexed family operators and function space ${}^A B$:**
  - **Set theory:** indexed union/intersection via range of restricted family; function space as maps from `A` into `B`
  - **Lean:** `noncomputable def IndexedUnion ...`; `noncomputable def IndexedIntersection ...`; `noncomputable def FunctionSpace ...`; `lemma FunctionSpace.Spec ...`
- [x] **Theorem 3J(a) (left inverse iff one-to-one, AC-free):**
  - **Set theory:** for `F : A → B` with `A` nonempty, `∃ G : B → A, G ∘ F = I_A` iff `F` is one-to-one
  - **Lean:** `theorem Set.thm_3Ja_left_inverse_iff_one_to_one ...` at the bottom of `Set/Ch3/S4_Functions.lean` in the plain `Set` namespace (the `Choice` namespace is reserved for declarations whose proofs *actually* use AC). The (⇒) direction uses the helper construction `noncomputable def LeftInverseRelation (F B a₀ : Set) : Set := F⁻¹ ∪ ((B - ran F) ⨯ Singleton a₀)` (also AC-free) and proves it is a function directly, plus `lemma one_to_one_preimage_unique ...`. A `#print axioms` check at the bottom of the file enforces AC-freeness.
- [x] **Theorem 3J(b) (right inverse iff onto, uses first-form AC):**
  - **Set theory:** for `F : A → B` with `A` nonempty, `∃ H : B → A, F ∘ H = I_B` iff `F` maps `A` onto `B`
  - **Lean:** `theorem Set.Choice.thm_3Jb_right_inverse_iff_onto ...` at the bottom of `Set/Ch3/S4_Functions.lean`, inside a reopened `namespace Choice` block. The file keeps textbook order while entering/exiting `Choice` only when needed: AC-free supporting results stay in plain `Set`, and only AC-invoking declarations are in `Choice`. A `#print axioms` check at the bottom enforces AC-dependence.
- [x] **Axiom of Choice (first form):**
  - **Set theory:** for any relation `R` there is a function `H ⊆ R` with `dom H = dom R` (Enderton p.49)
  - **Lean:** in-place in `Set/Ch3/S4_Functions.lean` as `def Set.ChoiceFirstForm` (AC-free statement in plain `Set`) plus `axiom Set.Choice.choice_first_form` (inside a short `namespace Choice` block). The file `#check`s these at Enderton's introduction point (p.49).

## Infinite Cartesian Products (pp. 54–55)

Primary files:
- `Set/Ch3/S5_InfiniteCartesianProducts.lean`
- `Set/Choice.lean`

- [x] **Definition (Infinite Cartesian product):**
  - **Set theory:** $\prod_{i \in I} H(i)=\{f \in {}^I(\bigcup \operatorname{ran}(H)) \mid \forall i \in I,\ f(i)\in H(i)\}$.
  - **Lean:** `noncomputable def InfiniteProduct (I H : Set) (hH : IsFunction H) (hIH : I ⊆ dom H) : Set := ...`
- [x] **Specification (InfiniteProduct.Spec):**
  - **Set theory:** $f \in \prod_{i \in I}H(i)$ iff $f$ is a function with domain $I$, codomain inside $\bigcup\operatorname{ran}(H)$, and each selected value belongs to the corresponding fiber.
  - **Lean:** `lemma InfiniteProduct.Spec {I H f : Set} (hH : IsFunction H) (hIH : I ⊆ dom H) : f ∈ InfiniteProduct I H hH hIH ↔ ...`
- [x] **Empty fiber implies empty product:**
  - **Set theory:** if some $H(i)=\varnothing$ with $i\in I$, then $\prod_{i\in I}H(i)=\varnothing$.
  - **Lean:** `theorem infiniteProduct_empty_of_empty_fiber ...`
- [x] **Axiom of Choice (second form):**
  - **Set theory:** For any set $I$ and function $H$ with $\operatorname{dom}(H)=I$, if every $H(i)$ is nonempty, then $\prod_{i \in I}H(i)\neq\varnothing$.
  - **Lean:** `def Set.ChoiceSecondForm : Prop := ...` (AC-free statement in `Set`), plus `axiom Set.Choice.choice_second_form : Set.ChoiceSecondForm` (in-place in `Set/Ch3/S5_InfiniteCartesianProducts.lean`)
- [x] **Derived theorem (ChoiceSecondForm gives nonempty product):**
  - **Set theory:** $\text{ChoiceSecondForm} \Rightarrow \forall I,H,\big((\forall i\in I,\ H(i)\neq\varnothing)\Rightarrow \prod_{i\in I}H(i)\neq\varnothing\big)$.
  - **Lean:** `theorem Set.choice_second_form_iff_infiniteProduct_nonempty : ...` (AC-free equivalence) and `theorem Set.Choice.infiniteProduct_nonempty_of_nonempty_fibers : ...` (AC-dependent consequence).
- [x] **Ch6S5 choice-form statement layer in `Set/Choice.lean`:**
  - **Set theory:** Theorem 6M forms (1), (2), (3), (4), and (6) as formal statements.
  - **Lean:** `ChoiceThirdForm`, `ChoiceFourthForm`, `ChoiceSixthForm` in `Set/Choice.lean`; `ChoiceFirstForm` and `ChoiceSecondForm` are now in-place in `Set/Ch3/S4_Functions.lean` and `Set/Ch3/S5_InfiniteCartesianProducts.lean` respectively (with Form (5), cardinal comparability, deferred to the future cardinal-comparison layer).

## Equivalence Relations (pp. 55–62)

Primary file: `Set/Ch3/S6_Equivalence.lean`

- [x] **Definition (Reflexive on a carrier):**
  - **Set theory:** $R$ is reflexive on $A$ iff $\forall x \in A,\ xRx$.
  - **Lean:** `def IsReflexiveOn (R A : Set) : Prop := ∀ {x}, x ∈ A → ⟪x, x⟫ ∈ R`
- [x] **Definition (Symmetric):**
  - **Set theory:** $\forall x\forall y,\ xRy \Rightarrow yRx$.
  - **Lean:** `def IsSymmetric (R : Set) : Prop := ∀ {x y}, ⟪x, y⟫ ∈ R → ⟪y, x⟫ ∈ R`
- [x] **Definition (Transitive relation):**
  - **Set theory:** $\forall x\forall y\forall z,\ (xRy \land yRz) \Rightarrow xRz$.
  - **Lean:** `def IsTransitiveRel (R : Set) : Prop := ∀ {x y z}, ⟪x, y⟫ ∈ R → ⟪y, z⟫ ∈ R → ⟪x, z⟫ ∈ R`
- [x] **Definition (Binary relation on a carrier):**
  - **Set theory:** $R$ is a relation and $R \subseteq A \times A$.
  - **Lean:** `def IsBinaryRelationOn (R A : Set) : Prop := IsRelation R ∧ R ⊆ (A ⨯ A)`
- [x] **Definition (Equivalence relation):**
  - **Set theory:** binary on $A$, reflexive on $A$, symmetric, transitive.
  - **Lean:** `def IsEquivalenceRelation (R A : Set) : Prop := IsBinaryRelationOn R A ∧ IsReflexiveOn R A ∧ IsSymmetric R ∧ IsTransitiveRel R`
- [x] **Theorem 3M (field-level equivalence):**
  - **Set theory:** if $R$ is a relation that is symmetric and transitive, then $R$ is an equivalence relation on $\operatorname{fld}(R)$.
  - **Lean:** `theorem thm_3M_symm_trans_is_equiv (R : Set) : IsRelation R → IsSymmetric R → IsTransitiveRel R → IsEquivalenceRelation R (fld R)`
- [x] **Definition (Equivalence class):**
  - **Set theory:** $[x]_R = \{t \in \operatorname{ran}(R) \mid xRt\}$.
  - **Lean:** `noncomputable def EquivalenceClass (x R : Set) : Set := ...`
- [x] **Specification (EquivalenceClass.Spec):**
  - **Set theory:** $t \in [x]_R \Leftrightarrow xRt$.
  - **Lean:** `lemma EquivalenceClass.Spec {x R t : Set} : t ∈ [x]₍R₎ ↔ ⟪x, t⟫ ∈ R`
- [x] **Lemma 3N (class equality criterion):**
  - **Set theory:** for $x,y \in A$, $[x]_R = [y]_R \Leftrightarrow xRy$.
  - **Lean:** `theorem lem_3N_equiv_class_eq_iff {R A x y : Set} (hEq : IsEquivalenceRelation R A) (hxA : x ∈ A) (hyA : y ∈ A) : [x]₍R₎ = [y]₍R₎ ↔ ⟪x, y⟫ ∈ R`
- [x] **Definition (Quotient set):**
  - **Set theory:** $A/R = \{[x]_R \mid x \in A\}$.
  - **Lean:** `noncomputable def QuotientSet (A R : Set) (_hEq : IsEquivalenceRelation R A) : Set := ...`, notation `A / R ∵ h` (the textbook's equivalence-relation hypothesis is built in as an explicit proof argument)
- [x] **Specification (QuotientSet.Spec):**
  - **Set theory:** $Q \in A/R \Leftrightarrow Q \in \mathcal P(\operatorname{ran}(R)) \land \exists x \in A,\ Q=[x]_R$.
  - **Lean:** `lemma QuotientSet.Spec_full {A R Q : Set} {hEq : IsEquivalenceRelation R A} : Q ∈ A / R ∵ hEq ↔ Q ∈ 𝒫 (ran R) ∧ ∃ x, x ∈ A ∧ Q = [x]₍R₎`
- [x] **Specification (QuotientSet.Spec, reduced form):**
  - **Set theory:** $Q \in A/R \Leftrightarrow \exists x \in A,\ Q=[x]_R$.
  - **Lean:** `lemma QuotientSet.Spec {A R Q : Set} {hEq : IsEquivalenceRelation R A} : Q ∈ A / R ∵ hEq ↔ ∃ x, x ∈ A ∧ Q = [x]₍R₎`
- [x] **Definition (Natural map):**
  - **Set theory:** $\varphi:A\to A/R$ is defined by $\varphi(x)=[x]_R$ for $x\in A$.
  - **Lean:** `noncomputable def NaturalMap (A R : Set) (hEq : IsEquivalenceRelation R A) : Set := ...` (the textbook's equivalence-relation hypothesis is built in as an explicit proof argument)
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
  - **Lean:** `theorem thm_3Q_compatible_exists_unique_quotient_map (R A F : Set) (hEqRel : IsEquivalenceRelation R A) (hCompat : IsCompatible F R A) : ∃! Fq, MapsInto Fq (A / R ∵ hEqRel) (A / R ∵ hEqRel) ∧ (∀ x (hxA : x ∈ A), ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ Fq)`
- [x] **Theorem 3Q (non-compatibility obstruction):**
  - **Set theory:** if $F$ is not compatible with $R$, no such induced quotient map exists.
  - **Lean:** `theorem thm_3Q_incompatible_not_exists_quotient_map (R A F : Set) (hEqRel : IsEquivalenceRelation R A) (hMap : MapsInto F A A) (hNot : ¬ IsCompatible F R A) : ¬ ∃ Fq, MapsInto Fq (A / R ∵ hEqRel) (A / R ∵ hEqRel) ∧ (∀ x (hxA : x ∈ A), ⟪[x]₍R₎, [F⟮x⟯]₍R₎⟫ ∈ Fq)`
- [x] **Definition (Partition):**
  - **Set theory:** nonempty blocks, pairwise disjoint unless equal, and exhaustive over $A$.
  - **Lean:** `def IsPartition (Pi A : Set) : Prop := ...`
- [x] **Theorem 3P (equivalence classes form a partition):**
  - **Set theory:** if $R$ is an equivalence relation on $A$, then $A/R$ is a partition of $A$.
  - **Lean:** `theorem thm_3P_equiv_classes_partition (R A : Set) (hEq : IsEquivalenceRelation R A) : IsPartition (A / R ∵ hEq) A`

## Ordering Relations (pp. 62–64)

Primary file: `Set/Ch3/S7_OrderingRelations.lean`

- [x] **Definition (Trichotomy on a carrier):**
  - **Set theory:** for any $x,y \in A$, exactly one of $xRy$, $x=y$, $yRx$ holds (encoded with exclusivity clauses).
  - **Lean:** `def TrichotomyOn (R A : Set) : Prop := ...`
- [x] **Definition (Linear ordering / total ordering):**
  - **Set theory:** a binary relation on $A$ that is transitive and satisfies trichotomy on $A$.
  - **Lean:** `def IsLinearOrder (R A : Set) : Prop := IsBinaryRelationOn R A ∧ IsTransitiveRel R ∧ TrichotomyOn R A`
- [x] **Definition (Irreflexive — name for Theorem 3R condition (i)):**
  - **Set theory:** there is no $x$ for which $xRx$.
  - **Lean:** `def IsIrreflexive (R : Set) : Prop := ∀ x, ⟪x, x⟫ ∉ R`
- [x] **Definition (Connected on $A$ — name for Theorem 3R condition (ii)):**
  - **Set theory:** for distinct $x,y \in A$, either $xRy$ or $yRx$.
  - **Lean:** `def IsConnectedOn (R A : Set) : Prop := ∀ x y, x ∈ A → y ∈ A → x ≠ y → (⟪x, y⟫ ∈ R ∨ ⟪y, x⟫ ∈ R)`
- [x] **Theorem 3R(i) (irreflexivity):**
  - **Set theory:** if $R$ linearly orders $A$, then there is no $x$ for which $xRx$.
  - **Lean:** `theorem thm_3R_i_linear_order_irreflexive (R A : Set) : IsLinearOrder R A → IsIrreflexive R`
- [x] **Theorem 3R(ii) (connectedness for distinct points):**
  - **Set theory:** if $R$ linearly orders $A$ and $x,y \in A$ with $x \ne y$, then $xRy \lor yRx$.
  - **Lean:** `theorem thm_3R_ii_linear_order_connected (R A : Set) : IsLinearOrder R A → IsConnectedOn R A`

---

# Chapter 4: Natural Numbers

## Inductive Sets (pp. 67–70)

- Primary file: `Set/Ch4/S1_InductiveSets.lean`
- [x] **Definition (Successor):**
  - **Set theory:** $a^+ = a \cup \{a\}$
  - **Lean:** `noncomputable def Successor (a : Set) : Set := a ∪ {a}`
- [x] **Definition (Inductive set):**
  - **Set theory:** $\text{Inductive}(A) \Leftrightarrow 0 \in A \land (\forall a \in A)\, a^+ \in A$
  - **Lean:** `def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A`
- [x] **Infinity axiom (primitive in Axioms; Enderton form derived in Ch4S1):**
  - **Set theory:** primitive witness form in the core axiom layer, with derived shorthand $\exists A\, \text{Inductive}(A)$
  - **Lean:** `axiom infinity : ∃ A, (∃ e, (∀ x, x ∉ e) ∧ e ∈ A) ∧ (∀ a, a ∈ A → ∃ s, (∀ x, x ∈ s ↔ x ∈ a ∨ x = a) ∧ s ∈ A)` in `Set/Axioms.lean`; derived theorem `theorem infinity_inductive : ∃ A, Inductive A` in `Set/Ch4/S1_InductiveSets.lean`; chosen witness `noncomputable def Infinity := Classical.choose infinity_inductive`; spec `lemma Infinity.Inductive : Inductive Infinity`
- [x] **Definition (Natural number):**
  - **Set theory:** $\text{Natural}(n) \Leftrightarrow (\forall A)\,(\text{Inductive}(A) \Rightarrow n \in A)$
  - **Lean:** `def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A`
- [x] **Theorem 4A (existence of $\omega$):**
  - **Set theory:** $\exists \omega\, \forall n\,(n \in \omega \Leftrightarrow \text{Natural}(n))$
  - **Lean:** `theorem thm_4A_natural_numbers_exist : ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n`
- [x] **Definition/Spec ($\omega$):**
  - **Set theory:** $n \in \omega \Leftrightarrow \text{Natural}(n)$
  - **Lean:** `noncomputable def ω := Classical.choose thm_4A_natural_numbers_exist`; `lemma ω.Spec {n : Set} : n ∈ ω ↔ Natural n`
- [x] **Membership conversion for $\omega$:**
  - **Set theory:** conversion between $n \in \omega$ and $\text{Natural}(n)$
  - **Lean:** `lemma ω.Spec {n : Set} : n ∈ ω ↔ Natural n` (used in both directions)
- [x] **Theorem 4B (minimal inductive set):**
  - **Set theory:** $\text{Inductive}(\omega)$ and $(\forall A)(\text{Inductive}(A) \Rightarrow \omega \subseteq A)$
  - **Lean:** `theorem thm_4B_ω_inductive : Inductive ω`; `theorem thm_4B_ω_subset_of_inductive : ∀ (A : Set), Inductive A → ω ⊆ A`
- [x] **Induction principle for $\omega$ (predicate form):**
  - **Set theory:** $\big(P(0)\land (\forall k\in\omega, P(k)\Rightarrow P(k^+))\big)\Rightarrow (\forall n\in\omega, P(n))$
  - **Lean:** `lemma ω_induction (P : Set → Prop) (hBase : P Set.Empty) (hStep : ∀ k, k ∈ ω → P k → P (k⁺)) : ∀ n, n ∈ ω → P n`
- [x] **Theorem 4C (nonzero naturals are successors):**
  - **Set theory:** $n \neq 0 \land \text{Natural}(n) \Rightarrow \exists m \in \omega\, (n = m^+)$
  - **Lean:** `theorem thm_4C_nonzero_natural_is_successor (n : Set) : n ≠ ∅ → Natural n → ∃ (m : Set), m ∈ ω ∧ n = m⁺`

## Peano's Postulates (pp. 70–73)

- Primary file: `Set/Ch4/S2_PeanosPostulates.lean` (proof order in file: 4E, 4F, 4G, then 4D; items below follow textbook order)
- [ ] **Definition (Peano system, Lean packaging):**
  - **Set theory:** triple $\langle N, S, e \rangle$ with $e \in N$, $S$ maps $N$ into $N$, $e \notin \operatorname{ran}(S)$ (no successor equals $e$), $S$ injective on $N$, and Peano induction on subsets of $N$
  - **Lean:** `def IsPeanoSystem (N : Set) (S : Set → Set) (e : Set) : Prop := e ∈ N ∧ (∀ n, n ∈ N → S n ∈ N) ∧ (∀ n, n ∈ N → S n ≠ e) ∧ (∀ m n, m ∈ N → n ∈ N → S m = S n → m = n) ∧ (∀ A : Set, A ⊆ N → e ∈ A → (∀ x, x ∈ A → S x ∈ A) → A = N)`
- [ ] **Lemma (successor is nonempty):**
  - **Set theory:** $a^+ \neq \varnothing$
  - **Lean:** `lemma successor_ne_empty (a : Set) : a⁺ ≠ ∅`
- [ ] **Definition (Transitive set):**
  - **Set theory:** $x \in a \land a \in A \Rightarrow x \in A$
  - **Lean:** `def IsTransitiveSet (A : Set) : Prop := ∀ (x a : Set), x ∈ a → a ∈ A → x ∈ A`
- [ ] **Theorem 4E ($\bigcup(a^+)$ for transitive $a$):**
  - **Set theory:** $a$ transitive $\Rightarrow \bigcup(a^+) = a$
  - **Lean:** `theorem thm_4E_bigunion_successor_of_transitive (a : Set) : IsTransitiveSet a → ⋃(a⁺) = a`
- [ ] **Theorem 4F (naturals are transitive sets):**
  - **Set theory:** $\text{Natural}(n) \Rightarrow n$ is a transitive set
  - **Lean:** `theorem thm_4F_natural_transitive_set (n : Set) : Natural n → IsTransitiveSet n`
- [ ] **Theorem 4G ($\omega$ transitive):**
  - **Set theory:** $\omega$ is a transitive set
  - **Lean:** `theorem thm_4G_omega_transitive_set : IsTransitiveSet ω`
- [ ] **Theorem 4D ($\omega$ is a Peano system):**
  - **Set theory:** $\langle \omega, \sigma, 0 \rangle$ is a Peano system (with successor on $\omega$)
  - **Lean:** `theorem thm_4D_omega_peano_system : IsPeanoSystem ω (fun n => n⁺) ∅`

## Recursion on $\omega$ (pp. 73–79)

Primary file: `Set/Ch4/S3_RecursionOnOmega.lean`  
Textbook extraction: `docs/textbook-transcriptions/ch4/ch4s3.md`

- [ ] **Definition (recursion solution, as a function-graph on $\omega$):** $h \subseteq \omega \times A$ is a total function from $\omega$ to $A$, sends $0 \mapsto a$, and satisfies the successor clause against $F : A \to A$.
  - **Lean:** `def RecursionSolution (h A a F : Set) : Prop := …`
- [ ] **Recursion theorem — existence:** Given $a \in A$ and $F : A \to A$ a function (encoded as `MapsInto F A A`), some $h$ satisfies `RecursionSolution`.
  - **Lean:** `theorem recursion_exists_on_ω (A a F : Set) : a ∈ A → MapsInto F A A → ∃ h, RecursionSolution h A a F`
- [ ] **Recursion theorem — uniqueness:** Any two solutions are equal as sets (hence the same function).
  - **Lean:** `theorem recursion_solution_unique (A a F h₁ h₂ : Set) (hF : MapsInto F A A) … : h₁ = h₂`
- [ ] **Recursion theorem — combined:** $\exists! h,\ \text{RecursionSolution}\,h\,A\,a\,F$.
  - **Lean:** `theorem recursion_theorem_on_ω (A a F : Set) : a ∈ A → MapsInto F A A → ∃! h, RecursionSolution h A a F`
- [ ] **Theorem 4H:** Every Peano system is isomorphic to $\langle \omega, \sigma, 0 \rangle$.
  - **Lean:** `def IsPeanoIsomorphism (f N : Set) (S : Set → Set) (e : Set) : Prop := …`; `theorem thm_4H_peano_isomorphic (N : Set) (S : Set → Set) (e : Set) : IsPeanoSystem N S e → ∃ f, IsPeanoIsomorphism f N S e`
## Arithmetic (pp. 79–83)

- Primary file: `Set/Ch4/S4_Arithmetic.lean`
- Textbook extraction: `docs/textbook-transcriptions/ch4/ch4s4.md`
- [ ] **Definition (Binary operation):** A function from $A \times A$ into $A$.
  - **Set theory:** a binary operation on $A$ is a function $A \times A \to A$
  - **Lean:** `def IsBinaryOperationOn (A op : Set) : Prop := MapsInto op (A ⨯ A) A`
- [ ] **Definition (Addition on $\omega$):** via recursion in the second argument.
  - **Set theory:** for fixed $m$, define $n \mapsto m+n$ by recursion with base $m+0=m$ and step $m+n^+=(m+n)^+$
  - **Lean:** `noncomputable def NatAdd (m n : Set) : Set`; `noncomputable instance : HAdd Set Set Set := ⟨NatAdd⟩`
- [ ] **Theorem 4I (A1/A2):**
  - $m + 0 = m$,
  - $m + n^+ = (m+n)^+$.
  - **Lean:** `theorem thm_4I_A1_add_zero ...`; `theorem thm_4I_A2_add_succ ...`
- [ ] **Definition (Multiplication on $\omega$):** via recursion.
  - **Set theory:** for fixed $m$, define $n \mapsto m\cdot n$ by recursion with base $m\cdot 0=0$ and step $m\cdot n^+=m\cdot n+m$
  - **Lean:** `noncomputable def NatMul (m n : Set) : Set`; `noncomputable instance : HMul Set Set Set := ⟨NatMul⟩`
- [ ] **Theorem 4J (M1/M2):**
  - $m \cdot 0 = 0$,
  - $m \cdot n^+ = m \cdot n + m$.
  - **Lean:** `theorem thm_4J_M1_mul_zero ...`; `theorem thm_4J_M2_mul_succ ...`
- [ ] **Definition/characterization (Exponentiation):**
  - $m^0 = 1$,
  - $m^{(n^+)} = m^n \cdot m$.
  - **Lean:** `noncomputable def NatPow (m n : Set) : Set`; `noncomputable instance : Pow Set Set := ⟨NatPow⟩`; `theorem nat_pow_zero …`; `theorem nat_pow_succ …`
- [ ] **Theorem 4K:** Basic arithmetic laws (assoc/comm/distrib) for $+$ and $\cdot$.
  - **Lean:** `theorem thm_4K_basic_arithmetic_laws ...`

## Ordering on $\omega$ (pp. 83–88)

- Primary file: `Set/Ch4/S5_OrderingOnOmega.lean`
- Textbook extraction: `docs/textbook-transcriptions/ch4/ch4s5.md`
- [ ] **Definition (order on $\omega$):** $m < n \Leftrightarrow m \in n$ and $m \le n \Leftrightarrow (m \in n \lor m=n)$.
  - **Set theory:** ordering is membership-based for von Neumann naturals.
  - **Lean:** `def NatLt (m n : Set) : Prop := m ∈ n`; `def NatLe (m n : Set) : Prop := m ∈ n ∨ m = n`
- [ ] **Lemma 4L(a):** $m \in n \Leftrightarrow m^+ \in n^+$.
  - **Set theory:** successor preserves and reflects strict order on naturals.
  - **Lean:** `theorem thm_4L_a_natural_succ_mem_iff (m n : Set) : m ∈ ω → n ∈ ω → (m ∈ n ↔ m⁺ ∈ n⁺)`
- [ ] **Lemma 4L(b):** no natural number is a member of itself.
  - **Set theory:** irreflexivity of `<` on $\omega$.
  - **Lean:** `theorem thm_4L_b_natural_not_mem_self (n : Set) : n ∈ ω → n ∉ n` (in `Set/Ch4/S5_OrderingOnOmega.lean`, reusing foundational theorem from S2)
- [ ] **Trichotomy law for $\omega$:** exactly one of $m \in n$, $m=n$, $n \in m$.
  - **Set theory:** any two naturals are linearly comparable under membership.
  - **Lean:** `theorem natural_trichotomy (m n : Set) : m ∈ ω → n ∈ ω → (m ∈ n ∨ m = n ∨ n ∈ m) ∧ ¬(m ∈ n ∧ m = n) ∧ ¬(m ∈ n ∧ n ∈ m) ∧ ¬(m = n ∧ n ∈ m)`
- [ ] **Corollary 4M:** for naturals, $m \in n \Leftrightarrow m \subset n$, and $m \le n \Leftrightarrow m \subseteq n$.
  - **Set theory:** strict/non-strict order corresponds to proper/non-proper inclusion.
  - **Lean:** `theorem cor_4M_mem_iff_proper_subset ...`; `theorem cor_4M_le_iff_subset ...`
- [ ] **Theorem 4N:** order preserved by addition, and by multiplication with nonzero factor.
  - **Set theory:** monotonicity of $+$ and $\cdot$ on $\omega$ (for nonzero multiplier in the multiplicative case).
  - **Lean:** `theorem thm_4N_order_preservation ...`
- [ ] **Corollary 4P:** cancellation laws for addition/multiplication on $\omega$.
  - **Set theory:** if $a+k=b+k$ then $a=b$; if $k\neq 0$ and $a\cdot k=b\cdot k$ then $a=b$.
  - **Lean:** `theorem cor_4P_cancellation ...`
- [ ] **Well ordering of $\omega$:** every nonempty subset of $\omega$ has a least element.
  - **Set theory:** every nonempty $A \subseteq \omega$ has minimal element under `<`.
  - **Lean:** `theorem omega_well_ordering ...`
- [ ] **Corollary 4Q:** no function $f:\omega\to\omega$ satisfies $f(n^+) \in f(n)$ for all $n$.
  - **Set theory:** there is no infinite strictly descending $\omega$-sequence.
  - **Lean:** `theorem cor_4Q_no_descending_omega_sequence ...`
- [ ] **Strong induction principle for $\omega$.**
  - **Set theory:** if every $n$ follows from truth on all smaller $m \in n$, then all naturals satisfy the predicate.
  - **Lean:** `theorem strong_induction_omega ...`

---

# Chapter 5: Construction of the Real Numbers

Primary files: `Set/Ch5/S1_Integers.lean`, `Set/Ch5/S2_RationalNumbers.lean`, `Set/Ch5/S3_RealNumbers.lean`, `Set/Ch5/S4_Summaries.lean`.

Enderton’s labels (5ZA, 5QA, 5RA, …) correspond to Lean names with Unicode subscripts where helpful: `thm_5ℤ…`, `thm_5ℚ…`, `thm_5ℝ…`. Some Chapter 5 proofs still use `sorry` or trivial `True` placeholders—see the `.lean` files.

## Integers (pp. 90–101)

- [ ] **Definition (difference-equivalence on $\omega \times \omega$):**
  - **Set theory:** $\langle m,n\rangle \sim \langle p,q\rangle \Leftrightarrow m+q=p+n$
  - **Lean:** `noncomputable def IntEqRel` with `IntEqRel.Spec`
- [ ] **Theorem 5ZA:** $\sim$ is an equivalence relation on $\omega \times \omega$.
  - **Lean:** `theorem thm_5ℤA : IntEqRel.IsEquivalenceRelation IntegerCarrier`
- [ ] **Definition (integers):** $\mathbb{Z} = (\omega \times \omega)/\sim$.
  - **Lean:** `noncomputable def IntegerCarrier : Set := ω ⨯ ω`; `noncomputable def IntegerSet : Set := IntegerCarrier / IntEqRel`; `notation "ℤ" => IntegerSet`
- [ ] **Lemma 5ZB (addition compatibility):** representative-level addition respects $\sim$.
  - **Lean:** `int_add_candidate_*`, `IntEqRel.pair_mem`, … (no separate `thm_5ZB`; used in `thm_5ℤF`)
- [ ] **Theorem 5ZC:** integer addition is commutative and associative.
  - **Lean:** `theorem thm_5ℤC : ∃ addZ, IntAddAxioms addZ` (derived from `thm_5ℤF`)
- [ ] **Theorem 5ZD:** $0_{\mathbb Z}$ is additive identity and additive inverses exist.
  - **Lean:** `theorem thm_5ℤD …`
- [ ] **Lemma 5ZE (multiplication compatibility):** representative-level multiplication respects $\sim$.
  - **Lean:** `int_mul_candidate_*`, … (bundled toward `thm_5ℤF`)
- [ ] **Theorem 5ZF:** integer addition/multiplication layer + distributivity packaging.
  - **Lean:** `theorem thm_5ℤF : …` (now has additive associativity and multiplicative identity proved; remaining `sorry` goals are multiplicative associativity, no-zero-divisors, and distributivity in `Set/Ch5/S1_Integers.lean`)
- [ ] **Theorem 5ZG:** multiplicative identity, $0_{\mathbb{Z}} \neq 1_{\mathbb{Z}}$, and no zero divisors.
  - **Lean:** `theorem thm_5ℤG …`
- [ ] **Lemma 5ZH (order compatibility):** representative-level order formula is well-defined under $\sim$.
  - **Lean:** subsumed in `IntOrderAxioms` / `lt_ℤ` infrastructure
- [ ] **Theorem 5ZI:** integer order is a linear ordering.
  - **Lean:** `theorem thm_5ℤI : ∃ ltZ, IntOrderAxioms ltZ`
- [ ] **Theorem 5ZJ:** integer order is preserved by addition and by multiplication with positive factor.
  - **Lean:** *not yet a standalone Enderton-titled theorem*
- [ ] **Corollary 5ZK:** cancellation laws on $\mathbb Z$.
  - **Lean:** *TBD as named corollary*
- [ ] **Theorem 5ZL:** embedding $E:\omega \to \mathbb{Z}$ preserves $+$, $\cdot$, and order.
  - **Lean:** *TBD*

## Rational Numbers (pp. 101–111)

- [ ] **Definition (fraction-equivalence on $\mathbb{Z} \times \mathbb{Z}'$):**
  - **Set theory:** $\langle a,b\rangle \approx \langle c,d\rangle \Leftrightarrow ad=cb$
  - **Lean:** `noncomputable def RatEqRel` (`Set/Ch5/S2_RationalNumbers.lean`)
- [ ] **Theorem 5QA:** $\approx$ is an equivalence relation on $\mathbb{Z} \times \mathbb{Z}'$.
  - **Lean:** `theorem thm_5ℚA : IsEquivalenceRelation RatEqRel (ℤ ⨯ ℤ')`
- [ ] **Definition (rationals):** $\mathbb{Q} = (\mathbb{Z} \times \mathbb{Z}')/\approx$.
  - **Lean:** `noncomputable def RationalSet : Set := (ℤ ⨯ ℤ') / RatEqRel`; `notation "ℚ" => RationalSet`
- [ ] **Lemma 5QB (addition compatibility):** fraction-level addition respects $\approx$.
  - **Lean:** `theorem lemma_5ℚB : True` (scaffold)
- [ ] **Theorem 5QC:** rational addition gives an Abelian group.
  - **Lean:** `theorem thm_5ℚC : ∃ addQ, RatAddAxioms addQ`
- [ ] **Lemma 5QD (multiplication compatibility):** fraction-level multiplication respects $\approx$.
  - **Lean:** `theorem lemma_5ℚD : True` (scaffold)
- [ ] **Theorem 5QE:** rational multiplication is associative/commutative/distributive.
  - **Lean:** `theorem thm_5ℚE : ∃ mulQ, RatMulAxioms mulQ`
- [ ] **Theorem 5QF:** every nonzero rational has a multiplicative inverse.
  - **Lean:** `theorem thm_5ℚF : True` (scaffold)
- [ ] **Corollary 5QG:** nonzero rationals are closed under multiplication.
  - **Lean:** `theorem cor_5ℚG : True` (scaffold)
- [ ] **Lemma 5QH (order compatibility):** order formula with positive denominators is well-defined.
  - **Lean:** `theorem lemma_5ℚH : True` (scaffold)
- [ ] **Theorem 5QI:** rational order is a linear ordering.
  - **Lean:** `theorem thm_5ℚI : ∃ ltQ, RatLtAxioms ltQ`
- [ ] **Theorem 5QJ:** rational order is preserved by addition and by multiplication with positive factor.
  - **Lean:** `theorem thm_5ℚJ : True` (scaffold)
- [ ] **Theorem 5QK:** cancellation laws on $\mathbb Q$.
  - **Lean:** `theorem thm_5ℚK : True` (scaffold)
- [ ] **Theorem 5QL:** embedding $E:\mathbb{Z} \to \mathbb{Q}$ preserves operations and order.
  - **Lean:** `theorem thm_5ℚL : True` (scaffold)

## Real Numbers (pp. 111–121)

- [ ] **Definition (Dedekind cut):**
  - **Set theory:** $x\subseteq\mathbb{Q}$, $x\neq\varnothing$, $x\neq\mathbb{Q}$, downward closed, no largest member.
  - **Lean:** `def IsDedekindCut (x : Set) : Prop := …`
- [ ] **Definition (reals as cuts):**
  - **Set theory:** $\mathbb{R}=\{x\subseteq\mathbb{Q}\mid x\text{ is a Dedekind cut}\}$
  - **Lean:** `noncomputable def RealSet : Set := …`
- [ ] **Definition (real order):**
  - **Set theory:** $x <_{\mathbb R} y \Leftrightarrow x \subset y$
  - **Lean:** `def RealLt (x y : Set) : Prop := x ⊆ y ∧ x ≠ y`
- [ ] **Theorem 5RA:** $<_{\mathbb R}$ is a linear ordering on $\mathbb R$.
  - **Lean:** `theorem thm_5ℝA : Set.IsLinearOrder RealOrderRel RealSet` (**`sorry`** in `Set/Ch5/S3_RealNumbers.lean`)
- [ ] **Theorem 5RB:** every nonempty bounded subset of $\mathbb R$ has a least upper bound.
  - **Lean:** `theorem thm_5ℝB : True` (scaffold)
- [ ] **Definition (real addition):** $x+_{\mathbb R}y=q+r\mid q\in x,\ r\in y$.
  - **Lean:** `noncomputable def RealAdd : Set := …`; `noncomputable def add_ℝ : Set → Set → Set := …`
- [ ] **Lemma 5RC:** if $x,y\in\mathbb R$, then $x+_{\mathbb R}y\in\mathbb R$.
  - **Lean:** `theorem lemma_5ℝC : True` (scaffold)
- [ ] **Theorem 5RD:** real addition is associative and commutative.
  - **Lean:** `theorem thm_5ℝD : True` (scaffold)
- [ ] **Theorem 5RE:** $0_{\mathbb{R}}\in\mathbb{R}$ and $x +_{\mathbb{R}} 0_{\mathbb{R}} = x$.
  - **Lean:** `theorem thm_5ℝE : True` (scaffold)
- [ ] **Theorem 5RF:** additive inverses on $\mathbb R$.
  - **Lean:** `theorem thm_5ℝF : True` (scaffold)
- [ ] **Corollary 5RG:** additive cancellation on $\mathbb R$.
  - **Lean:** `theorem cor_5ℝG : True` (scaffold)
- [ ] **Theorem 5RH:** real order preserved by addition.
  - **Lean:** `theorem thm_5ℝH : True` (scaffold)
- [ ] **Definition (real multiplication, sign-split Dedekind-cut form):**
  - **Lean:** `noncomputable def RealMul : Set := …`; `noncomputable def mul_ℝ : Set → Set → Set := …`
- [ ] **Theorem 5RI:** multiplication well-defined on reals; ordered-field laws; inverse for nonzero; positivity-preserving order.
  - **Lean:** `theorem thm_5ℝI : True` (scaffold)
- [ ] **Theorem 5RJ:** embedding $E:\mathbb{Q} \to \mathbb{R}$ preserves operations and order.
  - **Lean:** `theorem thm_5ℝJ : True` (scaffold)

## Summaries (pp. 121–123)

- [ ] **Definition (Abelian group / commutative ring with identity / integral domain / field / ordered field / complete ordered field):** chapter-level algebraic concept bundle.
  - **Lean:** `def IsAbelianGroupAdd …`, `IsCommutativeRingWithOne …`, `IsIntegralDomain …`, `IsFieldLike …`, `IsOrderedFieldLike …`, `IsCompleteOrderedFieldLike …` in `Set/Ch5/S4_Summaries.lean`

---

## Summary of Proven Items

Current checklist coverage: **Ch. 2, Ch. 3 through Functions (`S4`), and Ch. 4 § Inductive Sets (`S1`)** are marked checked from your human verification. From **Ch. 3 § Infinite Cartesian Products (`S5`)** and **Ch. 4 § Peano (`S2`) onward**, boxes are unchecked until explicitly re-verified.

| Chapter   | Total items | Checked |
| --------- | ----------- | ------- |
| Ch. 2     | 74          | 74      |
| Ch. 3     | 75          | 49      |
| Ch. 4     | 39          | 10      |
| Ch. 5     | 44          | 0       |
| **Total** | **232**     | **133** |
