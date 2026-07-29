# CS263 Project Writeup: Formalizing Enderton in Lean 4

Project repository: [Qinggao1729/axiomatic-set-theory](https://github.com/Qinggao1729/axiomatic-set-theory).  
Primary textbook: Herbert B. Enderton, *Elements of Set Theory*, Academic Press, 1977 ([publisher page](https://shop.elsevier.com/books/elements-of-set-theory/enderton/978-0-08-057042-6)).

> **Note.** This is the writeup submitted for CS 263 (Spring 2026). It describes the project as it stood at submission, and its detailed exposition covers the material audited by that point. The project has been extended since; the [README](README.md) is the current source of truth for scope and status.

## Purpose of the Project

The purpose of this project is to formalize Enderton's *Elements of Set Theory* in Lean 4, beginning with a primitive type of sets and a primitive membership relation, and then rebuilding the early parts of the textbook inside Lean. The project is not intended merely to reproduce familiar set-theoretic facts in another syntax. Its main aim is to use Lean to make textbook proofs more rigorous: every hidden side condition, omitted witness, domain assumption, and axiom dependency must be represented as a term that the kernel can check. The broader motivation is similar to other textbook formalization projects, such as formalizations of Tao's *Analysis*: natural-language mathematics is often correct, but it is compressed. A proof assistant forces every definition, every use of an axiom, and every side condition to be inspected. This helps disambiguate prose proofs, uncover hidden logical assumptions, and create a modular library that can support future work in mathematical logic.

One might ask why this project does not simply use Mathlib's existing set theory and already-proved theorems. Imports from Mathlib are minimized intentionally. Since the subject is a mathematical foundation, relying on a large library of higher-level mathematics would risk circularity at the level of exposition: the point is to rebuild the foundations rather than use a foundation already developed elsewhere. Moreover, many textbook theorems are likely already available in Mathlib in some form, so depending on them directly would defeat the pedagogical purpose of re-proving Enderton's development line by line. However, despite of the intention to serve as a mathematical foundation, this formalization is  unavoidably an explicit embedding of ZFC-style axiomatic set theory into dependent type theory. Lean's foundation is type-theoretic, whereas Enderton's textbook is written in an axiomatic set-theoretic language (specifically, ZFC).

## What I Formalized

Much of the code was produced with AI assistance, so I distinguish what is machine-checked from what I have audited by hand. The audited scope is Chapter 2, Chapter 3 Sections 1 through 7, and Chapter 4 Section 1: the sections I have reviewed for correctness, alignment with the textbook, and proof style. 

Within the audited sccope, chapter 2 introduces the primitive set-theoretic language and the basic axioms. Chapter 3 Sections 1 to 4 build ordered pairs, products, relations, n-ary relations, and functions. Chapter 4 Section 1 introduces inductive sets, the Infinity axiom, the set `ω` of natural numbers, and the induction principle on `ω`. (**Now Chapter 4 Sections 5 through 7 were completed audited, which include infinite Cartesian products, versions of the axiom of choice, equivalence relations and quotient sets, and linear orderings.**)

The project follows the textbook structure: each section has its own file, and the chapter files aggregate those section files in order. This makes the formalization easier to audit, easier to compare with the book, and easier to extend without losing the narrative order of the mathematics.

## Basic Axioms and Definitions

The formalization begins with a primitive universe of sets and a primitive membership relation:

```lean
axiom Set : Type

namespace Set

axiom ElementOf : Set → Set → Prop
infix:50 " ∈ " => ElementOf
infix:40 " ∉ " => fun x y => ¬ ElementOf x y

def Nonempty (A : Set) : Prop := ∃ x : Set, x ∈ A

@[simp] def SubsetOf (x a : Set) : Prop := ∀ t : Set, t ∈ x → t ∈ a
infix:50 " ⊆ " => SubsetOf
```

The core axioms are then stated as existential set-building principles:

```lean
axiom extensionality :  ∀ A B : Set, (∀ x : Set, x ∈ A ↔ x ∈ B) → A = B

axiom empty :  ∃ B : Set, ∀ x : Set, x ∉ B

axiom pairing :  ∀ u v : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x = u ∨ x = v

axiom union_preliminary :  ∀ a b : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ∈ a ∨ x ∈ b

axiom power :  ∀ a : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ⊆ a

axiom comprehension (P : Set → Prop) (c : Set) :  
    ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ∈ c ∧ P x

axiom union :  
    ∀ A : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ ∃ b : Set, b ∈ A ∧ x ∈ b

axiom infinity :  ∃ A : Set, 
    (∃ e : Set, (∀ x : Set, x ∉ e) ∧ e ∈ A) ∧
    (∀ a : Set, a ∈ A → ∃ s : Set, (∀ x : Set, x ∈ s ↔ x ∈ a ∨ x = a) ∧ s ∈ A)
```

In modern Enderton-style notation, the axiom of infinity is the familiar statement

```text
∃ A : Set, (∅ ∈ A ∧ (∀ a : Set, a ∈ A -> (a ∪ {a}) ∈ A)))
```

Many named sets are then constructed from existential axioms using `Classical.choose`. For example, the pair axiom gives a canonical pair set, and the corresponding specification lemma describes its membership condition:

```lean
noncomputable def Pair (u v : Set) : Set := Classical.choose (pairing u v)

@[simp] lemma Pair.Spec {u v x : Set} :
    x ∈ Pair u v ↔ x = u ∨ x = v :=
  (Classical.choose_spec (pairing u v)) x
```

This `*.Spec` pattern is central. It turns membership in a constructed set into a logical formula that Lean can simplify. For example, after unfolding `Pair.Spec`, a goal about `x ∈ Pair u v` becomes a goal about `x = u ∨ x = v`, which is often much easier to prove or simplify.

The project uses a custom simp attribute:

```lean
attribute [set_spec_simps] Pair.Spec
```

As the development proceeds, new membership specification lemmas are added to this attribute using the same command. This lets proofs use `simp only [set_spec_simps]` or `simp_all only [set_spec_simps]` to unfold many set specifications consistently without listing them one by one. In the audited scope, important examples include `Empty.Spec`, `Pair.Spec`, `Singleton.Spec`, `Power.Spec`, `Union.Spec`, `Comprehension.Spec`, `Intersection.Spec`, `Difference.Spec`, `BigUnion.Spec`, `BigIntersection.Spec`, `OrderedPair.Spec`, `Product.Spec`, `Product.Pair.Spec`, `Domain.Spec`, `Range.Spec`, `Field.Spec`, `Identity.Spec`, `Inverse.Spec`, `Inverse.Pair.Spec`, `Composition.Spec`, `Composition.Pair.Spec`, `Restriction.Spec`, `Restriction.Pair.Spec`, `Image.Spec`, and `ω.Spec`.

The ordered pair is defined using Kuratowski's construction:

```lean
noncomputable def OrderedPair (x y : Set) : Set :=
  Pair (Singleton x) (Pair x y)

notation:90 "⟪" x ", " y "⟫" => OrderedPair x y
```

Lean already uses angle brackets `⟨...⟩` for constructor syntax, such as witnesses for conjunctions and existentials. Using `⟪x, y⟫` makes ordered pairs visually distinct from Lean's built-in proof-constructor syntax.

Functions are represented as special relations:

```lean
def IsFunction (F : Set) : Prop :=
  IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟪x, y⟫ ∈ F
```

In Chapter 4 Section 1, successor and inductive sets are defined as:

```lean
noncomputable def Successor (a : Set) : Set := a ∪ Singleton a
postfix:90 "⁺" => Successor

def Inductive (A : Set) : Prop :=
  ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A
```

The set of natural numbers is then obtained by Theorem 4A:

```lean
theorem thm_4A_natural_numbers_exist :
    ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n := by
  ...

noncomputable def ω := Classical.choose thm_4A_natural_numbers_exist

@[simp]
lemma ω.Spec {n : Set} : n ∈ ω ↔ Natural n := by
  ...
```

## Important Theorems

The audited part of the project contains several important theorem families. The first is the no-universal-set theorem:

```lean
theorem thm_2A_no_universal_set :
    ¬ ∃ (A : Set), ∀ (x : Set), x ∈ A := by
  ...
```

This theorem is important not only as a result from Chapter 2, but also as a warning for later constructions. For example, arbitrary intersections require attention to nonemptiness assumptions precisely because an unrestricted "intersection of an empty family" would behave like a universal set, which cannot exist here.

In function theory, one central theorem is Enderton's Theorem 3G, whose first part says that if `F` is one-to-one and `x ∈ dom F`, then `F⁻¹(F(x)) = x`. In Lean, the theorem appears with explicit proof obligations attached to the function-value notation:

```lean
theorem thm_3G_one_to_one_inverse (F : Set) :
    ∀ hOne : IsOneToOne F,
    ∀ x, ∀ hx : x ∈ dom F,
    F⁻¹⟮F⟮x⟯'(⟨hOne.1, hx⟩)⟯'(
      ⟨(inv_is_function F hOne),
      (image_mem_dom_inverse F hOne.1 x hx)⟩)
    = x := by
  ...
```

This theorem is especially useful for explaining the project's design around function values, so it is discussed in detail later.

Theorem 3J is another important example because it separates an AC-free theorem from an AC-dependent theorem. The left-inverse statement is AC-free:

```lean
theorem thm_3J_a_left_inverse_iff_one_to_one
    (F A B : Set) (hMap : MapsInto F A B) (hANon : A.Nonempty) :
    (∃ G, MapsInto G B A ∧ (G ∘ F) = Identity A) ↔ IsOneToOne F := by
  ...
```

The right-inverse statement uses AC and is therefore placed inside `namespace Choice`:

```lean
namespace Choice

theorem thm_3J_b_right_inverse_iff_onto
    (F A B : Set) (hMap : MapsInto F A B) (_ : A.Nonempty) :
    (∃ H, MapsInto H B A ∧ (F ∘ H) = Identity B) ↔ MapsOnto F A B := by
  ...

end Choice
```

In Chapter 4 Section 1, the key results are the existence of `ω`, the fact that `ω` is inductive, the minimality of `ω`, and the induction principle:

```lean
theorem thm_4A_natural_numbers_exist :
    ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n := by
  ...

theorem thm_4B_ω_inductive : Inductive ω := by
  ...

theorem thm_4B_ω_subset_of_inductive :
    ∀ (A : Set), Inductive A → ω ⊆ A := by
  ...

lemma ω_induction (P : Set → Prop)
    (hBase : P Set.Empty)
    (hStep : ∀ k, k ∈ ω → P k → P (k⁺)) :
    ∀ n, n ∈ ω → P n := by
  ...
```

The theorem that every nonzero natural number is a successor is then proved using this induction principle:

```lean
theorem thm_4C_omega_exists_successor (n : Set) :
    n ≠ ∅ → Natural n → ∃ (m : Set), m ∈ ω ∧ n = m⁺ := by
  ...
```

Together, these examples show the arc of the audited development: Chapter 2 establishes basic set-theoretic constraints, Chapter 3 builds relation and function theory, and Chapter 4 Section 1 begins the construction of natural numbers and induction on `ω`.

## Design Choices

### Simp Policy: `*.Spec` Lemmas

The project deliberately tags canonical specification lemmas as simplification rules. These lemmas have a natural simplifying direction: membership in a constructed set is reduced to the defining condition of that set. For example, `Pair.Spec` changes a membership goal into an equality disjunction, and `Domain.Spec` changes membership in a domain into the existence of a related output.

This is different from tagging commutativity theorems as simp rules. For example, a union commutativity theorem `A ∪ B = B ∪ A` does not have a natural simplifying direction: both sides have the same complexity. This is analogous to why Lean's built-in theorem `Or.comm` is not used as a global simplification rule. Rewriting `P ∨ Q` to `Q ∨ P` is sometimes useful, but it is not simplification in a canonical direction. Therefore, commutativity lemmas are kept as ordinary theorems and invoked explicitly when needed.

The custom attribute `set_spec_simps` supports this policy. As new definitions are introduced, their canonical membership lemmas can be registered:

```lean
attribute [set_spec_simps] Pair.Spec
```

Then proofs can use `simp only [set_spec_simps]`or `simp_all only [set_spec_simps]`. This makes proof scripts shorter without making them opaque. The simplification step is still conceptually meaningful: it is unfolding definitions into their membership specifications, not searching through arbitrary algebraic rewrite rules.

### Proof Style, Automation, and Pedagogy

The proof style is designed for readability and pedagogy. Foundational proofs should first expose their visible structure: use `intro` for implications, `constructor` for conjunctions and biconditionals, and `extensionality` for equality of sets. Routine logical work can then be discharged by `simp`, especially with `set_spec_simps`, but the conceptual mathematical steps should remain visible.

Automation is deliberately limited. Powerful techniques such as `aesop`, `ring`, and `linarith` are avoided in final proofs of foundational material, except as temporary tools for exploration. If `aesop?` suggests a proof idea, the final script should usually be rewritten into explicit structural steps plus controlled simplification. The same principle applies to complicated `exact` or `apply` clauses: long one-line proof terms are avoided when a few short steps would be more readable.

This reflects an unresolved but productive tension between automation and readability. The right amount of automation improves both proof-writing speed and readability, because it prevents the script from being overwhelmed by trivial propositional bookkeeping. Too much automation, however, hides the mathematical reason a theorem is true. Conversely, writing out every trivial step can obscure the main argument and make the proof harder to read. The project therefore uses a middle policy: automate routine logical normalization, but keep the proof's mathematical skeleton explicit.

There is also a contrast with a common maintainability recommendation from [Mathlib's style guide](https://leanprover-community.github.io/contribute/style.html#squeezing-simp-calls): do not "squeeze" `simp` calls by replacing them with the output of `simp?`, because broad `simp` calls can remain stable under changes to definitions and local context. That recommendation is important for large library maintenance. This project, however, has a pedagogical goal: it is a textbook formalization where readers should see why a proof works. Therefore, the project does not follow the maintainability-first convention rigidly. In some cases, explicit small steps are preferred even if a single `simp` could solve the goal. However, the right boundary of automation is still under investigation as the boundary changes as proofs become more and more complex. 

### Axiom Placement and the Non-Linearity of AC

Another design choice concerns where axioms should live. For ordinary set-theoretic axioms, keeping them in a central primitive file is clearer for readers and imports. It gives the development a single place where the basic assumptions can be inspected. Later section files then import those axioms and derive section-specific forms, such as the derivation of `∃ A, Inductive A` from the primitive Infinity axiom.

The Axiom of Choice requires a more delicate treatment because it is nonconstructive and because Enderton's exposition is not perfectly linear from a formalization perspective. The textbook uses a form of AC in Chapter 3 Section 4, in the proof that every surjective function has a right inverse (Theorem 3J(b)), before later discussing the equivalent forms of AC in a more systematic way. If the formalization waited to introduce AC until that later discussion, Chapter 3 Section 4 could not follow the book's proof order. The solution is to put AC forms in a dedicated file, `Set/Choice.lean`, and then `#check` the relevant form in the section where the textbook first uses it. This keeps AC available for earlier theorems without hiding it as an ordinary background fact. Since AC is nonconstructive, the project also makes its use visible through namespaces: declarations that necessarily use AC (such as Theorem 3J(b)) are placed inside `namespace Choice`, while AC-free theorems stay in the ordinary `Set` namespace.

### Function-Value Notation in a Relation-Based Formalization

This project includes a deliberate design experiment: introducing textbook-style function-value notation in a relation-based set-theoretic development. The goal is to remain close to Enderton's presentation while preserving Lean's requirement that every term be well-formed at elaboration time. This choice affects the mathematical definition of `F(x)`, the notation design, its relation to existing ZF-style library practice, and the order in which proof obligations must appear.

In the set-theoretic definition used by the textbook, `F(x)` denotes the unique `y` such that `⟪x, y⟫ ∈ F`. This notation is meaningful only under two preconditions: first, `F` must be a function; second, `x` must belong to `dom F`. Thus `F(x)`is a value only after these two conditions are justified. The uniqueness of that value follows from the function property.

The original style was intentionally concise and foundational. It reasoned directly with `IsFunction F` and with pair-membership statements such as `⟪x, y⟫ ∈ F`, rather than introducing value terms:

```lean
def IsValueAt (F x y : Set) : Prop := IsFunction F ∧ ⟪x, y⟫ ∈ F
```

This approach is mathematically clean and proof-oriented, but it is less aligned with textbook statements such as `F⁻¹(F(x)) = x`. To align more closely with Enderton's notation, the project introduces a core value definition, an automatic notation form, and a manual proof-explicit notation form:

```lean
noncomputable def FunctionValue
    (F x : Set) (hF : IsFunction F) (hxdom : x ∈ dom F) : Set :=
  Classical.choose (hF.2 x hxdom)

noncomputable def FunctionValueAuto
    (F x : Set)
    (hF : IsFunction F := by simp_all!)
    (hxdom : x ∈ dom F := by simp_all!) : Set :=
  FunctionValue F x hF hxdom

notation:max F "⟮" x "⟯" => FunctionValueAuto F x

noncomputable def FunctionValueWithProof
    (F x : Set) (h : IsFunction F ∧ x ∈ dom F) : Set :=
  FunctionValue F x h.1 h.2
```

The manual notation is written as `F⟮x⟯'p`, where `p : IsFunction F ∧ x ∈ dom F`. This allows concise packaging of proof obligations as `⟨hF, hxdom⟩`. The automatic form `F⟮x⟯` is convenient when Lean can infer the function and domain obligations from the local context. Here the parenthesis in `F⟮x⟯` is different from the regular parenthesis `F(x)`.

The notation design is also modeled on Lean's indexing idiom. Lean supports an automatic indexing form such as `xs[i]`, but if the index-validity proof is not discharged automatically, the user can provide an explicit proof using a manual form such as `xs[i]'p`. The function-value notation follows the same two-mode structure: `F⟮x⟯` is the automatic mode, and `F⟮x⟯'p` is the manual mode. The automatic mode improves usability when local context is sufficient; the manual mode preserves predictability and proof transparency when automation is insufficient. Explicit proofs in `F⟮x⟯'p` are often mathematically substantive.

The current project intentionally keeps automatic discharge conservative, using `simp_all!` only. This avoids two extremes: automation that is too strong and silently proves mathematically interesting facts, and automation that is too weak to recognize straightforward local hypotheses.

The central case study is Theorem 3G. The textbook proof order is:

1. assume `F` is one-to-one and `x ∈ dom F`;
2. derive `⟪x, F(x)⟫ ∈ F`;
3. derive `⟪F(x), x⟫ ∈ F⁻¹`;
4. derive `F(x) ∈ dom F⁻¹`;
5. use Theorem 3F to conclude `F⁻¹` is a function;
6. infer the conclusion `F⁻¹(F(x)) = x`.

The Lean theorem is:

```lean
theorem thm_3G_one_to_one_inverse (F : Set) :
    ∀ hOne : IsOneToOne F,
    ∀ x, ∀ hx : x ∈ dom F,
    F⁻¹⟮F⟮x⟯'(⟨hOne.1, hx⟩)⟯'(
      ⟨inv_is_function F hOne, image_mem_dom_inverse F hOne.1 x hx⟩)
    = x := by
  intro hOne x hx
  have hF : IsFunction F := hOne.1
  have hxy : ⟪x, F⟮x⟯⟫ ∈ F := by
    simpa using FunctionValue.Spec F x hOne.1 hx
  have hyxInv : ⟪F⟮x⟯, x⟫ ∈ F⁻¹ := (Inverse.Pair.Spec).2 hxy
  exact FunctionValue.eq_of_pair (F := F⁻¹) (x := F⟮x⟯) (y := x) (inv_is_function F hOne) hyxInv
```

In Lean, proof order is constrained by term formation. Steps 5 and 4 must already be available when writing the outer value term `F⁻¹⟮F⟮x⟯...⟯...` in the theorem statement. Therefore, proof obligations that are rhetorically postponed in textbook prose move to the front as elaboration requirements. The body of the proof then carries out the graph argument corresponding to textbook Steps 2, 3, and 6.

The four proof objects embedded in the statement are:

1. `hOne.1 : IsFunction F`, validating the inner application;
2. `hx : x ∈ dom F`, also validating the inner application;
3. `inv_is_function F hOne : IsFunction (F⁻¹)`, corresponding to textbook Step 5 but required earlier;
4. `image_mem_dom_inverse F hOne.1 x hx : F⟮x⟯ ∈ dom (F⁻¹)`, corresponding to textbook Step 4 but required earlier.

Together, these make the composite term syntactically admissible in Lean. Inside the proof body, `FunctionValue.Spec` establishes the graph membership `⟪x, F⟮x⟯⟫ ∈ F`; `Inverse.Pair.Spec` turns this into `⟪F⟮x⟯, x⟫ ∈ F⁻¹`; and `FunctionValue.eq_of_pair` concludes the value equality.

So the Lean proof uses Steps 1, 5, and 4 up front to validate notation in the theorem statement, then derives Steps 2, 3, and 6 in the proof body. This is the central order mismatch: textbook exposition can delay validity checks, but Lean cannot delay type-correctness of notation.

The current section-level policy is therefore hybrid. In `Set/Ch3/S4_Functions.lean`, the project prioritizes textbook-style value notation as a deliberate experiment. From `Set/Ch3/S5_InfiniteCartesianProducts.lean` onward, theorem statements may prefer the lighter predicate style `IsValueAt F x y` unless explicit value notation is pedagogically important. The reason is that later theorem statements become denser, and statement-level value obligations can harm readability and refactorability. However, this may be improved in the future by writing stronger tactics for the automatic mode.

## Lean-Enforced Rigor: Concrete Examples

The project repeatedly encounters places where Lean forces mathematically important details to be explicit.

First, comprehension requires an explicit ambient set. In Lean, a comprehension object is constructed from a predicate `(P : Set → Prop)` and a carrier `(c : Set)`, not from `P` alone. The textbook may omit the container either because the container is obvious or because the existence of container is obvious, but the Lean proof must still provide it.

Second, arbitrary intersection arguments `⋂X` require `X` being non-empty. Without a nonemptiness assumption, `X` can lead to a universal-set interpretation, which is blocked by Theorem 2A (`thm_2A_no_universal_set`). Lean forces this boundary to be explicit when the textbook may omit it because it is trivial.

Third, function application is a rigor point both for explicit value notation and for the `IsValueAt` predicate. Writing `F(x)` in the textbook may omit verification that `F` is a function or that `x ∈ dom F`, because those facts are obvious from context. In Lean, they must be supplied. The same is true when using `IsValueAt F x y` Thus, function values are another instance of the same principle: objects and statements are only meaningful when their construction data are present.

These examples explain one of the central claim of the project. Formalization does not merely confirm final theorems; it exposes hidden assumptions in standard proofs and upgrades them to explicit verified structure.

## Future Work

Future work is to continue formalizing the remaining sections and chapters, while maintaining the same standards of traceability, readability, and explicit dependency control used in the audited scope of this report.

One major future task is to improve tactics for the automatic mode of `F⟮x⟯`. The current implementation uses conservative automation, but stronger targeted tactics might discharge routine `IsFunction` and domain obligations without hiding mathematically substantive work.

Another future issue concerns arithmetic in the set-theoretic constructions of `ℤ`, `ℚ`, and `ℝ`. One possible exception to the policy of minimizing Mathlib imports would be to import `Mathlib.Tactic` for arithmetic equalities and inequalities. However, using tactics such as `ring` effectively would likely require registering the custom integer, rational, and real constructions as instances of Mathlib algebraic typeclasses such as `CommSemiring`. This is debatable because those structures are themselves the objects being constructed inside the set-theoretic development; registering them as typeclasses may create a mismatch between the custom set-theoretic universe and Mathlib's typeclass hierarchy.

A further future challenge is non-linearity in the textbook. AC is one example, but it is not the only one. Enderton uses cardinality in Chapter 6, while a fully set-theoretic definition of cardinal numbers using ordinals appears only near the end of Chapter 7. A formalization must decide whether to introduce later notions early in side files, use temporary interfaces, or reorganize the proof order. This is another instance where formalization makes textbook dependency structure explicit.

## Contribution and Acknowledgment

This project is an independent continuation and expansion of Enderton formalization work in Lean. The direct upstream inspiration is [claby2/axiomatic-set-theory](https://github.com/claby2/axiomatic-set-theory), and I have already received approval from the original author to continue this line of development. The current repository's structure, ongoing proofs, and design decisions are maintained in [Qinggao1729/axiomatic-set-theory](https://github.com/Qinggao1729/axiomatic-set-theory), with Enderton's text as the mathematical reference. Besides proving more theorems, the main difference in this project is structural and methodological: the formalization is organized section by section, with each textbook section assigned to its own Lean file. This makes the repository closer to the book, easier to audit, and better suited for future extension.