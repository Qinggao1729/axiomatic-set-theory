# Design Choices

Rationale for the foundational and representational decisions in this project.
Where `proof_style.md` says *how* to write a proof, this document explains *why*
certain modeling choices were made. These are about faithfulness of the
reduction to set theory, not about day-to-day proof formatting.

## Metalogic vs. Object Theory: Do Dependent Types Break the Axiomatic Approach?

Short answer: **no.** Dependent function types (`∀ (h : P), Q`) and dependent
pair types (`∃ (h : P), Q`) live in the *metalogic*, not in the set theory being
axiomatized, and they add zero set-theoretic axioms.

### The two layers

The project keeps a clean separation:

- **Object theory** — the thing being formalized: a single type `Set` with a
  relation `∈` and the ZF axioms (extensionality, separation, pairing, union,
  power, infinity, ...) stated as Lean `axiom`s / constructions. This is the set
  theory.
- **Metalogic** — the ambient language we *speak in*: Lean's dependent type
  theory (CIC) plus classical logic. This is the medium, exactly as ordinary
  mathematical prose plus first-order logic is the medium in Enderton's book.

The constructs `∀ (h : P), Q`, `∃ (h : P), Q`, `Prop`, `∧`, `→` are all
metalogic. Writing `∀ A : Set, A ⊆ N → ...` uses the metalogic to *talk about*
sets; it does not posit a new set. Dependent types therefore enlarge the
set-theoretic commitments no more than the words "for all" do in the textbook.

### Why the dependent binders are harmless

For a `Prop`-valued `P`, proof irrelevance means a proof of `P` carries no
information beyond "`P` holds." Consequently:

- `∀ (h : P), Q` is literally `P → Q` when `Q` does not mention `h`;
- `∃ (h : P), Q` is literally `P ∧ Q` when `Q` does not mention `h`.

They only look exotic when `Q` *uses the proof to denote a set* — which is what
the rejected value form of `IsClosedUnder` did:
`S⟮x⟯'(⟨hS, hA x hx⟩)` fed proofs into `FunctionValue` to pick out a set. Even
there, the *binder* introduces no axiom; the dependency is just bookkeeping. So
the complexity later removed was an **ergonomics** problem, never a
**soundness/foundations** problem.

### What actually affects the axiom budget

Two things genuinely do, and neither is the dependent type:

1. **Classical choice.** `FunctionValue` is `Classical.choose (...)`, so the
   value form pulls in `Classical.choice`. The image form `S⟦A⟧ ⊆ A` avoids that
   particular use. (Mathlib's baseline trio — `propext`, `Classical.choice`,
   `Quot.sound` — is already in play regardless.)
2. **Comprehension as a single higher-order axiom.** In textbook FOL-ZF,
   Separation is an *axiom schema* (one instance per formula). In Lean it is one
   axiom quantifying over all predicates `Set → Prop`. That impredicative,
   second-order flavor is a more substantive departure from pure FOL-ZF than any
   `Σ`/`Π` type is.

Audit what any theorem actually rests on with `#print axioms thm_4D`; that is the
purpose of `Set/AxiomIndex.md`.

### The purist caveat

A strict reductionist claim ("ZF is *the* foundation, with nothing underneath")
would require the metalogic to be plain first-order logic. Lean's type theory is
a different (and in places stronger) foundation, so a proof assistant is never a
*pure* FOL-ZF reduction — it is always "ZF formalized inside type theory plus
classical logic." That is a property of using any proof assistant, not something
dependent pairs introduced, and it does not conflict with this project's goal: a
machine-checked, pedagogical companion that makes axiom dependencies explicit.

Net: prefer the image form `S⟦A⟧ ⊆ A` for ergonomics, track `Classical.choice`
and the comprehension axiom via `#print axioms` / `AxiomIndex.md`, and treat the
`∀ (h : ...)` / `∃ (h : ...)` machinery as foundationally inert.

## Building Function-Sets: `FunFromRel` vs `GraphOn`, and Faithful Reduction

The recursion theorem and the Peano-system definition consume a genuine
function-*set* (a single-valued set of ordered pairs), but the operations we feed
them are most naturally described by a *rule* ("send `n` to `n⁺`"). There are two
ways to turn a rule into a set, and the choice is not cosmetic: it decides how
much type-theoretic structure leaks into objects that are supposed to be pure
sets. This project uses `FunFromRel` and deliberately avoids the earlier
`GraphOn`.

### The two builders

- `GraphOn (A : Set) (f : Set → Set) := {⟪x, f x⟫ | x ∈ A}` takes a **Lean
  operation** `f : Set → Set`.
- `FunFromRel (A B : Set) (φ : Set → Set → Prop) := {⟪a, b⟫ ∈ A ⨯ B | φ a b}`
  takes a **meta-relation** `φ : Set → Set → Prop` and an explicit codomain `B`.

Concretely, the successor operator is `GraphOn ω (·⁺)` versus
`FunFromRel ω ω (fun a b => b = a⁺)`.

### Why `FunFromRel` is the more faithful reduction

The goal of the project is to *reduce* mathematics to set theory: a function
should be nothing more than a single-valued set of pairs, with its function-hood
*proved* from the axioms, not assumed.

- *Single-valuedness: proved, not borrowed.* A Lean `f : Set → Set` is, by the
  ambient type theory, automatically total and single-valued. `GraphOn` silently
  imports those two properties — the very content of "this relation is a
  function" — for free. `FunFromRel` takes a relation `φ` that may relate one `a`
  to many `b`; to obtain `MapsInto (FunFromRel A B φ) A B` one must supply
  `∀ a ∈ A, ∃! b ∈ B, φ a b` (`FunFromRel.mapsInto`). That obligation is exactly
  Enderton's side condition for a relation to be a function, discharged with set
  axioms rather than smuggled in from Lean.
- *Existence by Separation, not Replacement.* Because every pair of
  `FunFromRel A B φ` is bounded in advance by `A ⨯ B`, the set exists by
  Separation alone. `GraphOn`'s `{⟪x, f x⟫ | x ∈ A}` has no a priori codomain
  bound, so justifying it set-theoretically really needs Replacement (collect the
  image `{f x | x ∈ A}` first). Demanding the codomain `B` keeps the axiom
  footprint minimal and explicit.
- *Honest dependency tracking.* With `GraphOn`, the kernel records no use of the
  function being single-valued, because that fact never entered the proof — it
  was definitional. With `FunFromRel`, the single-valuedness lemma is a real
  hypothesis, so `#print axioms` / proof structure reflects what the mathematics
  actually depends on.

`GraphOn` is not *wrong* — it produces the same set — it is just a pragmatic
shortcut that leans on type theory for the part that set theory is supposed to
prove. `FunFromRel` is one notch closer to the bare set-theoretic story while
staying convenient.

### Shallow vs deep embedding (the wider lens)

The `GraphOn`/`FunFromRel` choice is a small instance of a general spectrum for
representing one formal system (here, first-order set theory) inside a host (Lean's
type theory).

- **Shallow embedding.** Object-language constructs map directly onto host
  constructs: a formula *is* a Lean `Prop`, a defining condition *is* a Lean
  predicate. This project is shallow: Separation is
  `comprehension (P : Set → Prop) (c : Set) : ∃ B, ∀ x, x ∈ B ↔ x ∈ c ∧ P x`,
  where the object-language "property" is the host predicate `P`. `GraphOn`'s
  `f : Set → Set` and `FunFromRel`'s `φ : Set → Set → Prop` are the same idea at
  the term/relation level. Shallow is concise and inherits the host's automation,
  but you cannot quantify over or inspect formulas, and you silently inherit host
  features (e.g. a `P` built with `Classical.choice` is admissible here, which is
  stronger than Enderton's syntactic Separation schema).
- **Deep embedding.** Object-language syntax is reified as data (`inductive
  Formula`) with an interpreter (`Satisfies : Env → Formula → Prop`). Then
  Separation can be stated as a genuine schema over syntax:
  `separation_schema (φ : Formula) … : ∃ B, ∀ x, x ∈ B ↔ x ∈ c ∧ Satisfies … φ`.
  This is maximally faithful — you can reason *about* the language (induct on
  `Formula`, define provability, prove reflection, ask which separations are
  first-order definable) — but every concrete use carries de Bruijn/interpreter
  overhead and loses direct tactic support.

Where this lands: a shallow embedding is the right default for a companion that
*formalizes the theorems* of a textbook — it keeps proofs readable and lets Lean's
tactics work. Moving from `GraphOn` to `FunFromRel` is a faithfulness improvement
*within* the shallow style: instead of borrowing single-valuedness from a Lean
arrow, functions are built from a relation and the function axioms are discharged
as set-theoretic obligations. A full deep embedding would only pay off for a
different project — proving *meta-theorems about* ZFC (independence, the
Separation/Replacement schemas as schemas, reflection) — not for formalizing
Enderton's results.

## `F⟮x⟯` / `FunctionValue` unification timeouts

A consequence of the function-application notation `F⟮x⟯`: because its value is
extracted from a side-condition proof via `Classical.choose`, reconciling two
independently-built occurrences can blow the `maxHeartbeats` budget. This is the
proof-complexity cost of the value form (the same cost that motivates preferring
pair-membership / image statements; see the function-representation guidance in
`proof_style.md`).

This documents a `maxHeartbeats` timeout that can arise from the automatic
function-application notation. The live example is `Set/Ch3/S6_Equivalence.lean`
(theorem 3Q, uniqueness branch), which uses the recommended fix below, so the code
there no longer shows the failure — this note preserves the reasoning.

### Setup

`F⟮x⟯` is notation that expands to
`FunctionValue F x ⟨by function_eval_auto, by function_eval_auto⟩`. Two facts about
this expansion drive the problem:

- Each written occurrence carries its own `by function_eval_auto` tactic blocks, so
  it independently *re-runs* the search that proves the side conditions
  `IsFunction F` and `x ∈ dom F`. The notation has no cache; nothing is shared
  between occurrences.
- `FunctionValue` is defined as `FunctionValue F x h := Classical.choose (h.1.2 x h.2)`,
  i.e. its value is extracted from the side-condition proof `h` via `Classical.choose`
  (this is also why it is `noncomputable`).

### What goes wrong

When two independently-written `F⟮x⟯` occurrences must be reconciled — e.g. one is
fed to a lemma like `function_value_unique` whose argument type forces it to match
another — the searches typically produce *different* proof terms `h₁` and `h₂`, and
the unifier is left having to check `FunctionValue F x h₁ = FunctionValue F x h₂`.

For reference, the lemma's signature is:

```lean
lemma function_value_unique (F x y z : Set) (hF : IsFunction F) :
    ⟪x, y⟫ ∈ F → ⟪x, z⟫ ∈ F → y = z
```

The reconciliation happens because the final argument has type `⟪x, z⟫ ∈ F`: when
you pass a hypothesis whose value already contains one `F⟮x⟯` term, `z` must unify
with it, so writing a *second* `F⟮x⟯` for `z` forces the comparison of two
independently-built `FunctionValue` terms.

That equation is *true*, and it is *decidable*: by proof irrelevance `h₁` and `h₂`
are interchangeable, and `isDefEq` always terminates. The two terms are therefore
**comparable, not incomparable** — the issue is purely that the cheap route is not
taken, so it needs far more time than the heartbeat budget allows. Concretely the
proof-irrelevance shortcut fails to fire because `FunctionValue F x h` unfolds to
`Classical.choose (h.1.2 x h.2)`, which is:

- **opaque** — `Classical.choose` is irreducible (there is no algorithm that
  computes its value), so the two terms never reduce to a common normal form that
  the unifier could compare directly; and
- **embeds `h`** — once unfolded, the proof `h` is no longer a clean top-level
  argument of `FunctionValue`; it lives *inside* the argument to `Classical.choose`
  (as `h.1.2 x h.2`). The cheap "both arguments are proofs ⇒ equal by proof
  irrelevance" rule applies only at a top-level argument position, so it no longer
  fires; the unifier instead digs into the buried subterm and reduces the `dom F`
  comprehension machinery appearing in the proofs' types.

The unifier then delta-unfolds and grinds until it exceeds `maxHeartbeats`. (In
principle a large enough `maxHeartbeats` would let it finish, confirming this is a
budget overrun, not an impossibility.)

### Where the error is reported

`maxHeartbeats` is cumulative over a tactic block, so the timeout is frequently
*blamed* on a later step — `subst`, `exact`, even a `rcases` in the next branch —
than the term-building step that actually burned the budget. Do not trust the
reported line; fix the occurrence that builds the heavy term.

### Fixes

1. **Keep both side-condition facts in context** (recommended). Add
   `have hFfun : IsFunction F := ...` and `have hxDomF : x ∈ dom F := ...` before
   the `F⟮x⟯` uses. Every `function_eval_auto` then closes by assumption and builds
   the *same* proof term `⟨hFfun, hxDomF⟩`, so all `F⟮x⟯` occurrences become
   syntactically identical and unify trivially. This keeps `F⟮x⟯` notation uniform
   across the proof.
2. **Pass the argument as `_`.** Instead of writing a second `F⟮x⟯`, pass `_` and
   let Lean unify the metavariable with an `F⟮x⟯` term already present in a
   hypothesis (e.g. the membership fact handed to `function_value_unique`). No
   second term is built, so neither the re-search nor the opaque comparison happens.
   Leaner, but breaks notation uniformity.

Prefer (1) for readability and uniform notation; use (2) when minimizing extra
`have`s matters.
