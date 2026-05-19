# Ch4 Section 1 (Inductive Sets) — Textbook Extraction

Source: Enderton, *Elements of Set Theory*, Chapter 4 "Inductive Sets",
pp. 67–70 (`Enderton_Textbook.pdf`).

This transcription tracks the set-theoretic content used to formalize the
section in `Set/Ch4/S1_InductiveSets.lean`. Definitions and theorem
statements are reproduced verbatim (with light typographic normalization);
proofs are sketched in the order Enderton gives them.

## 1. Motivation (p.67)

> First we need to define natural numbers as suitable sets. Now numbers do
> not at first glance appear to be sets. […] Nevertheless, we can construct
> specific sets that will serve perfectly well as numbers. In fact this can
> be done in a variety of ways.

- **Zermelo (1908).** Take the natural numbers to be
`∅, {∅}, {{∅}}, …`.
- **von Neumann (standard).** Make each natural number be the set of all
smaller natural numbers. Concretely:
  - `0 = ∅`
  - `1 = {∅} = {0}`
  - `2 = {0, 1} = {∅, {∅}}`
  - `3 = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}`

Two "extraneous" properties drop out for free:

> `0 ∈ 1 ∈ 2 ∈ 3 ∈ …` and `0 ⊆ 1 ⊆ 2 ⊆ 3 ⊆ …`.

Enderton calls these "accidental side effects of the definition" that
"do no harm, and actually will be convenient at times". We rely on them
heavily in Ch4 §5 (the order on `ω`).

## 2. Successor, inductive sets, infinity (p.68)

> **Definition.** For any set `a`, its *successor* `a⁺` is defined by
> `a⁺ = a ∪ {a}`.
>
> A set `A` is said to be *inductive* iff `∅ ∈ A` and it is "closed under
> successor," i.e., `(∀a ∈ A) a⁺ ∈ A`.

In terms of the successor operation, the first few natural numbers are

> `0 = ∅,  1 = ∅⁺,  2 = ∅⁺⁺,  3 = ∅⁺⁺⁺, …`

(Exercise 1 shows these are pairwise distinct.) Enderton observes that
"although we have not yet given a formal definition of 'infinite,' we can
see informally that any inductive set will be infinite," and that no
prior axiom forces an infinite set into existence. The **Infinity Axiom**
fixes that:

> **Infinity Axiom.** There exists an inductive set:
> `(∃A)[∅ ∈ A ∧ (∀a ∈ A) a⁺ ∈ A]`.

## 3. Natural numbers and Theorem 4A (p.68–69)

> **Definition.** A *natural number* is a set that belongs to every
> inductive set.
>
> **Theorem 4A.** There is a set whose members are exactly the natural
> numbers.

**Proof (Enderton).**

> Let `A` be an inductive set; by the infinity axiom it is possible to
> find such a set. By a subset axiom there is a set `w` such that for any
> `x`,
>
> `x ∈ w ⇔ x ∈ A & x belongs to every other inductive set`
>       `⇔ x belongs to every inductive set`.

(Same structure as the proof of Theorem 2B: one fixed witness from the
existence axiom, then a comprehension carve-out.)

## 4. `ω` and Theorem 4B (p.69)

> The set of all natural numbers is denoted by a lowercase Greek omega:
>
> `x ∈ ω ⇔ x is a natural number`
>       `⇔ x belongs to every inductive set`.
>
> In terms of classes, we have
>
> `ω = ⋂{A | A is inductive}`,
>
> but the class of all inductive sets is not a set.

> **Theorem 4B.** `ω` is inductive, and is a subset of every other
> inductive set.

**Proof (Enderton).**

> First of all, `∅ ∈ ω` because `∅` belongs to every inductive set. And
> second,
>
> `a ∈ ω  ⇒  a belongs to every inductive set`
>        `⇒  a⁺ belongs to every inductive set`
>        `⇒  a⁺ ∈ ω`.
>
> Hence `ω` is inductive. And clearly `ω` is included in every other
> inductive set.

Since `ω` is itself inductive, `0 (= ∅)` is in `ω`, as are `1, 2, 3`;
"unnecessary extraneous objects have been excluded from `ω`, since `ω`
is the *smallest* inductive set". The two halves of 4B (closure +
minimality) are exactly what powers induction:

> **Induction Principle for `ω`.** Any inductive subset of `ω` coincides
> with `ω`.
>
> Suppose, for example, that we want to prove that for every natural
> number `n`, the statement `__n__` holds. We form the set
>
> `T = {n ∈ ω | __n__}`
>
> of natural numbers for which the desired conclusion is true. If we can
> show that `T` is inductive, then the proof is complete. Such a proof
> is said to be a *proof by induction*.

This is the template every later inductive proof in Enderton (and in
this formalization) follows.

## 5. Theorem 4C (p.69)

> **Theorem 4C.** Every natural number except 0 is the successor of some
> natural number.

**Proof (Enderton).**

> Let `T = {n ∈ ω | either n = 0 or (∃p ∈ ω) n = p⁺}`. Then `0 ∈ T`. And
> if `k ∈ T`, then `k⁺ ∈ T`. Hence by induction, `T = ω`.

The proof is a one-line application of the Induction Principle for `ω`:
the predicate `P(n) := (n = 0) ∨ (∃ p ∈ ω, n = p⁺)` is trivially
inductive (`P(0)` is the left disjunct; `P(k) → P(k⁺)` is the right
disjunct via `p := k`), so it holds on all of `ω`. Any nonzero `n ∈ ω`
must then satisfy the right disjunct.

## 6. Lean mapping (`Set/Ch4/S1_InductiveSets.lean`)


| Book                     | Lean                                                                                                                                                    |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Successor `a⁺ = a ∪ {a}` | `noncomputable def Successor (a : Set) : Set := a ∪ Singleton a`                                                                                        |
| Inductive set            | `def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A`                                                                                         |
| Infinity axiom           | Primitive form in `Set/Axioms.lean`: `axiom infinity : ∃ A, (∃ e, (∀ x, x ∉ e) ∧ e ∈ A) ∧ (∀ a, a ∈ A → ∃ s, (∀ x, x ∈ s ↔ x ∈ a ∨ x = a) ∧ s ∈ A)`; Enderton-style form derived in `Set/Ch4/S1_InductiveSets.lean` as `theorem infinity_inductive : ∃ A, Inductive A` |
| Chosen inductive set     | `noncomputable def Infinity : Set := Classical.choose infinity_inductive`; `lemma Infinity.Inductive : Inductive Infinity`                             |
| Natural number           | `def Natural (n : Set) : Prop := ∀ A, Inductive A → n ∈ A`                                                                                              |
| Theorem 4A               | `theorem thm_4A_natural_numbers_exist : ∃ ω, ∀ n, n ∈ ω ↔ Natural n`                                                                                      |
| Definition of `ω`        | `noncomputable def ω := Classical.choose thm_4A_natural_numbers_exist`; `@[simp] lemma ω.Spec : n ∈ ω ↔ Natural n`                                      |
| Theorem 4B (inductive)   | `theorem thm_4B_ω_inductive : Inductive ω`                                                                                                                |
| Theorem 4B (minimality)  | `theorem thm_4B_ω_subset_of_inductive : ∀ A, Inductive A → ω ⊆ A`                                                                                         |
| Induction principle      | `lemma ω_induction (P : Set → Prop) (hBase : P ∅) (hStep : ∀ k ∈ ω, P k → P (k⁺)) : ∀ n ∈ ω, P n`                                                       |
| Theorem 4C               | `theorem thm_4C_omega_exists_successor : n ≠ ∅ → Natural n → ∃ m, m ∈ ω ∧ n = m⁺`                                                                        |


### Axiom-layer placement note

Enderton states the Infinity Axiom on p.68 using the literal predicate
`∅ ∈ A ∧ (∀a ∈ A) a⁺ ∈ A`. In this repo, the primitive Infinity axiom
lives in `Set/Axioms.lean` in witness-expanded form (empty witness `e`
and successor witness `s`), and `Set/Ch4/S1_InductiveSets.lean` derives
the Enderton-style statement as `infinity_inductive : ∃ A, Inductive A`
after `Empty`, `Successor`, and `Inductive` are defined.

## 7. Proof-flow notes

- **4A** mirrors the textbook one-to-one: pick `Infinity` as a fixed
inductive set, then comprehension defines
`w = {x ∈ Infinity | x ∈ every other inductive set}`. The
`x ∈ w ↔ Natural x` biconditional unfolds by the same case-split as the
book (`B = Infinity` vs `B ≠ Infinity`).
- **4B (inductive half)** is unfolded by hand following the book's
three-step chain `a ∈ ω → a belongs to every inductive set → a⁺ belongs to every inductive set → a⁺ ∈ ω`.
- **4B (minimality half)** is the immediate consequence of
`ω.Spec` + `Natural`.
- **Induction principle** is packaged as `ω_induction`: given `P` on
`Set`, we build `T = {n ∈ ω | P n}` exactly as in the book, show `T`
inductive, conclude `ω ⊆ T` by minimality, and extract `P n` from any
`n ∈ ω`.
- **4C** is now a direct one-application use of `ω_induction` with
`P n := n = ∅ ∨ ∃ m ∈ ω, n = m⁺`, matching the textbook "by
induction, `T = ω`" line.

