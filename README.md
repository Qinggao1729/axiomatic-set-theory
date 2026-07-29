# Axiomatic Set Theory in Lean 4

A machine-checked formalization of Herbert Enderton's *Elements of Set Theory*, built from two primitives — `Set : Type` and `ElementOf : Set → Set → Prop` — up through the ZF axioms, elementary constructions, relations, functions, the Axiom of Choice, quotients, orderings, the natural numbers `ω`, and induction on `ω`. See the complete checklist [here](TODO.md).

The goal is not to reprove known mathematics as fast as possible. It is to build a **pedagogical companion to the textbook in which nothing is hidden**: every definitional side condition is a proof obligation the user must discharge, every use of the Axiom of Choice is visible in the type, and every construction is traceable to the axiom it came from. Where the textbook says "for every *nonempty* set `A`, define `⋂A`", the Lean definition takes a proof of nonemptiness as an argument, and you cannot write `⋂A` without it.

| | |
|---|---|
| **Source text** | Herbert B. Enderton, *Elements of Set Theory* |
| **Scope** | Ch. 2, Ch. 3, Ch. 4 §1 — all human-audited against the text |
| **Size** | 258 declarations, of which 173 are theorems and lemmas |
| **`sorry` / `admit`** | none |
| **Build** | `lake build` completes clean |

Written for CS 263 (Programming Languages, Prof. Max Willsey, UC Berkeley) and substantially extended afterward. The [project report](CS263%20Project%20Report.md) covers the design in prose.

Reproduce the size figures with:

```bash
rg "^\s*(private\s+)?(noncomputable\s+)?(theorem|lemma|def|abbrev|axiom|instance)\s" \
   --glob "Set/**/*.lean" --no-filename | wc -l
```

---

## The Primitive Layer

Everything in the repository is built from the following, and nothing else. This is `Set/Axioms.lean` in full apart from its comments and the `namespace Set` wrapper — a file that imports nothing at all — so the entire set of assumptions fits on one screen:

```lean
axiom Set : Type                                    -- the universe of sets
axiom ElementOf : Set → Set → Prop                  -- the membership relation

infix:50 " ∈ " => ElementOf
infix:40 " ∉ " => fun x y => ¬ ElementOf x y

@[simp] def SubsetOf (x a : Set) : Prop := ∀ t : Set, t ∈ x → t ∈ a
infix:50 " ⊆ " => SubsetOf
```

`Set` and `ElementOf` are the only undefined notions; `⊆` is already a definition rather than a primitive. On top of them sit the axioms, each stated as an existential claim and cited to its page in Enderton:

```lean
-- [Ch2 §1, p.17] Extensionality
axiom extensionality : ∀ A B : Set, (∀ x : Set, x ∈ A ↔ x ∈ B) → A = B

-- [Ch2 §1, p.18] Empty set
axiom empty : ∃ B : Set, ∀ x : Set, x ∉ B

-- [Ch2 §1, p.18] Pairing
axiom pairing : ∀ u v : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x = u ∨ x = v

-- [Ch2 §1, p.18] Union, preliminary binary form
axiom union_preliminary : ∀ a b : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ∈ a ∨ x ∈ b

-- [Ch2 §1, p.18] Power set
axiom power : ∀ a : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ⊆ a

-- [Ch2 §1, p.21] Subset (Separation / Aussonderung)
axiom comprehension (P : Set → Prop) (c : Set) :
  ∃ B : Set, ∀ x : Set, x ∈ B ↔ x ∈ c ∧ P x

-- [Ch2 §2, p.24] Union, full form
axiom union : ∀ A : Set, ∃ B : Set, ∀ x : Set, x ∈ B ↔ ∃ b : Set, b ∈ A ∧ x ∈ b

-- [Ch4 §1, p.68] Infinity, stated with explicit witnesses `e` (empty) and `s` (successor)
axiom infinity :
  ∃ A : Set,
    (∃ e : Set, (∀ x : Set, x ∉ e) ∧ e ∈ A) ∧
    (∀ a : Set, a ∈ A → ∃ s : Set, (∀ x : Set, x ∈ s ↔ x ∈ a ∨ x = a) ∧ s ∈ A)
```

Each axiom asserts only that *some* set exists with the stated members; none of them names one. Every canonical object in the library is therefore introduced by the same three steps — the existential axiom, a `noncomputable def` naming a witness through `Classical.choose`, and a `*.Spec` inversion lemma recovering the membership condition. For the power set axiom above, in `Set/Ch2/S1_Axioms.lean`:

```lean
noncomputable def Power (A : Set) : Set := Classical.choose (power A)

@[simp] lemma Power.Spec {A x : Set} : x ∈ Power A ↔ x ⊆ A :=
  (Classical.choose_spec (power A)) x
```

Uniqueness is a separate result proved from extensionality (`power_eq_power`), not something `Classical.choose` supplies.

The **Axiom of Choice is deliberately absent** from `Set/Axioms.lean`. It is introduced at the point the textbook introduces it, in a quarantined namespace, as described in [§5 below](#5-visible-axiom-of-choice-boundaries-enforced-at-build-time).

## What Is Technically Distinctive

### 1. Proof-carrying definitions: preconditions live in the type

Enderton defines many objects only under a hypothesis. Rather than defining a total function and proving side lemmas later, the hypothesis becomes an argument, so **every call site must discharge it**.

```lean
-- `⋂A` exists only for nonempty `A`, so the proof is an argument:
noncomputable def BigIntersection (A : Set) (hA : A.Nonempty) : Set :=
  Classical.choose (intersection A hA)

-- Comprehension needs a carrier set — no unrestricted `{x | P x}`:
noncomputable def Comprehension (P : Set → Prop) (c : Set) : Set :=
  Classical.choose (comprehension P c)

-- The quotient `A / R` exists only when `R` is an equivalence relation on `A`:
noncomputable def QuotientSet (A R : Set) (_hEq : IsEquivalenceRelation R A) : Set
```

For quotients this is exposed through custom notation `A / R ∵ h`, where `∵` reads "because" and marks `h` as a *proof* argument, visually distinct from set-valued subscripts like `[x]₍R₎`. An `app_unexpander` prints it back in that form in goal states rather than showing raw application.

### 2. Function application as a checked operation

In set theory `F(x)` is only meaningful when `F` is a function and `x ∈ dom F`. The notation `F⟮x⟯` makes both conditions **mandatory side goals**, deliberately mirroring Lean's own array indexing (`xs[i]` vs. `xs[i]'p`):

```lean
noncomputable def FunctionValue (F x : Set) (h : IsFunction F ∧ x ∈ dom F) : Set :=
  Classical.choose (h.1.2 x h.2)

macro_rules
  | `($F⟮$x⟯)      => `(FunctionValue $F $x ⟨by function_eval_auto, by function_eval_auto⟩)
  | `($F⟮$x⟯'($p)) => `(FunctionValue $F $x $p)   -- pass the proof directly
```

`F⟮x⟯` discharges the obligation by tactic; `F⟮x⟯'(p)` takes the proof explicitly. The obligation is never silently dropped.

### 3. Custom automation with controlled, laddered simplification

`function_eval_auto` is a hand-written tactic that discharges those side conditions. It is deliberately structured as a **ladder from cheapest and most predictable to broadest**, so foundational proofs are not closed by opaque search when a targeted rewrite suffices:

```lean
macro_rules
  | `(tactic| function_eval_auto) => `(tactic|
    solve
    | assumption
    | solve_by_elim
    | simp only [function_eval_sideconds, prop_simps]
    | simp only [set_spec_simps, function_eval_sideconds, prop_simps]
    | simp_all only [function_eval_sideconds, prop_simps]
    ...
    | aesop)
```

It is backed by three purpose-built simp attribute sets (`Set/SimpAttrs.lean`) rather than a global simp set:

- `set_spec_simps` — the `*.Spec` membership characterizations, such as `Comprehension.Spec : x ∈ Comprehension P c ↔ x ∈ c ∧ P x`,
- `prop_simps` — propositional normalization used in `simp only` mode, such as `and_true` and `iff_true`,
- `function_eval_sideconds` — bridge lemmas such as `MapsInto F A B → IsFunction F`.

Side-condition lemmas are registered as `aesop safe forward` rather than `safe apply`, because forward chaining from a concrete `MapsInto` hypothesis instantiates metavariables that backward search would have to guess, and a fact derived once is reused across every later `F⟮x⟯` goal. The reasoning is recorded in-file at the declaration site.

### 4. Quantifying over proof obligations when the search needs them in scope

Because `F⟮x⟯` triggers a proof search at elaboration time, a definition whose body *contains* an application must put the side-condition proofs in scope at that point. In the infinite Cartesian product, 
```lean
/-
[Enderton Ch3 §5, p.54] "Let `I` be a set ... and let `H` be a function whose
domain includes `I` ... We define
`⨉_{i ∈ I} H(i) = { f | f is a function with domain I and (∀ i ∈ I), f(i) ∈ H(i) }`."
-/
```
the two textbook clauses ("`f` is a function", "`dom f = I`") therefore become `∃`-bound proofs inside the comprehension predicate:

```lean
noncomputable def InfiniteProduct (I H : Set) (hH : IsFunction H) (hIH : I ⊆ dom H) : Set :=
  Comprehension
    (fun f =>
      ∃ (hFfun : IsFunction f), ∃ (hDomF : (dom f) = I),
        ∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯)
    (𝒫 (I ⨯ ⋃ (ran H)))
```

Writing the same clauses as a plain conjunction `IsFunction f ∧ (dom f) = I ∧ ∀ i (hiI : i ∈ I), f⟮i⟯ ∈ H⟮i⟯` *fails to elaborate*: as sibling conjuncts they are not local hypotheses, so automation cannot see them when `f⟮i⟯` is checked. The failed version is kept commented out beside the definition with that explanation. This is the first point in the development where quantifying over proof obligations is forced.

### 5. Visible Axiom-of-Choice boundaries, enforced at build time

Choice-dependent results are quarantined in a `Choice` namespace, and the split is checked by the compiler rather than asserted in prose. Enderton's Theorem 3J(a) and 3J(b) are adjacent in the same file with parallel statements, but only (b) needs AC:

```lean
theorem thm_3Ja_left_inverse_iff_one_to_one
    (F A B : Set) (hMap : MapsInto F A B) (hANon : A.Nonempty) :
    (∃ G, MapsInto G B A ∧ (G ∘ F) = Identity A) ↔ IsOneToOne F

-- declared inside `namespace Choice`
theorem thm_3Jb_right_inverse_iff_onto
    (F A B : Set) (hMap : MapsInto F A B) (hANon : A.Nonempty) :
    (∃ H, MapsInto H B A ∧ (F ∘ H) = Identity B) ↔ MapsOnto F A B
```

Two queries at the bottom of `Set/Ch3/S4_Functions.lean` turn that claim into a build-time check:

```lean
#print axioms thm_3Ja_left_inverse_iff_one_to_one
#print axioms Choice.thm_3Jb_right_inverse_iff_onto
```

The build output shows the difference:

```
'Set.thm_3Ja_left_inverse_iff_one_to_one' depends on axioms:
  [Set, propext, Classical.choice, Quot.sound, Set.ElementOf,
   Set.comprehension, Set.extensionality, Set.pairing, Set.power,
   Set.union, Set.union_preliminary]

'Set.Choice.thm_3Jb_right_inverse_iff_onto' depends on axioms:
  [... same list ...,
   Set.Choice.choice_first_form]     ← AC, and only here
```

Any future edit that drags AC into 3J(a), or removes it from 3J(b), changes this output. AC forms are introduced at their textbook appearance (Form I in §4, Form II in §5) and named as separate objects (`ChoiceFirstForm`, `ChoiceSecondForm`) so that equivalence proofs can later be added as ordinary theorems following the textbook.

### 6. Reduction discipline: set-theoretic functions are sets

From Chapter 2 onward a function is an object *of the universe* — a set of ordered pairs — never a Lean arrow `Set → Set`. A Lean `f : Set → Set` is, by the ambient type theory, automatically total and single-valued, which would silently import the very content of "this relation is a function." So function-hood is always a hypothesis to be discharged:

```lean
def IsFunction (F : Set) : Prop :=
  IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟪x, y⟫ ∈ F

def MapsInto (F A B : Set) : Prop :=
  IsFunction F ∧ (dom F) = A ∧ (ran F) ⊆ B
```

Every theorem takes the function as a `Set` parameter carrying `IsFunction` / `MapsInto` / `IsOneToOne` as the textbook requires. Lean arrows are reserved for genuinely meta-level roles that are not function-objects: axiom schemas and property quantification (`comprehension (P : Set → Prop)`, `ω_induction (P : Set → Prop)`), the primitive relation `ElementOf`, and meta-indexed families. The reasoning, including shallow vs. deep embedding and why dependent types do not compromise the axiomatic approach, is in [`design_choices.md`](design_choices.md).

### 7. Dependency structure is explicit and traceable

- `Set/Axioms.lean` holds the primitive layer and nothing else: `Set`, `ElementOf`, and the ZF axioms. AC is deliberately *not* here.
- `Set/AxiomIndex.md` maps every axiom to its first appearance in Enderton (chapter, section, page) and its declaration site in code.
- Canonical objects follow one uniform pattern — existential axiom → `noncomputable def` via `Classical.choose` → a `*.Spec` membership lemma.
- The Infinity axiom is stated primitively in witness-expanded form, and Enderton's shorthand `∃ A, Inductive A` is derived as a theorem rather than assumed.
- Doc-comments carry literal textbook wording with page citations, e.g. `[Enderton Ch3 §4, p.43]`, so any declaration can be checked against the source.

---

## Trust Model

What is actually guaranteed, and what is not:

**Verified mechanically.** `lake build` completes with no errors. There are no `sorry` or `admit` occurrences anywhere under `Set/` — every stated theorem has a complete proof accepted by the Lean kernel.

**Human-audited.** Every section in the repository has been reviewed line by line against the textbook for faithfulness of statements, doc-comment accuracy, and proof readability. Machine-checking is necessary but not sufficient: a proof can be accepted by the kernel while stating something subtly different from the theorem in the book, so statement wording is checked by hand against the page it cites.

**Intentional axioms.** Twelve, all deliberate: the two primitives and the eight ZF axioms listed under [The Primitive Layer](#the-primitive-layer) above, plus two forms of Choice (`choice_first_form`, `choice_second_form`) declared at their textbook appearance. These are the object theory being formalized, not gaps. `Set/AxiomIndex.md` maps each one to its page in Enderton and its declaration site.

**Known caveats.** Prose documents can lag the code after refactors — when they disagree, trust the `.lean` files and the build. Comprehension is formalized as a single higher-order axiom over Lean predicates rather than a first-order axiom *schema*, which is a genuine (and documented) departure from textbook FOL-ZF; see [`design_choices.md`](design_choices.md). 

---

## Ownership and Attribution

Being precise about this, since the project mixes several sources:

**Herbert Enderton** — the mathematics. All definitions, theorem statements, and proof strategies follow *Elements of Set Theory*. Doc-comments quote the text with page citations. 

**[claby2/axiomatic-set-theory](https://github.com/claby2/axiomatic-set-theory)** — earlier Lean formalization of Enderton-style set theory that inspired this line of work and some early structure, notably the primitive layer and the `Classical.choose` + `*.Spec` idiom. This repository has since been substantially expanded and reorganized. See [`ACKNOWLEDGMENTS.md`](ACKNOWLEDGMENTS.md).

**Lean 4 and Mathlib** — the proof assistant and tactic ecosystem (`simp`, `aesop`, `solve_by_elim`). The dependency is deliberately thin: across the whole development the only external imports are tactics and `Mathlib.Logic.Basic`, both in `Set/Ch2/S1_Axioms.lean`, and `Set/Axioms.lean` imports nothing at all. None of Mathlib's set theory or its `ZFSet` development is used; the material is rebuilt from the primitives.

**AI assistance** — used as a drafting tool inside a [workflow](workflow.md) I designed and enforced: literal page-image transcription of each section (kept local, as the textbook is under copyright), first-pass formalization, and page-cited doc-comments under a numbered naming convention. Model output does not follow the written guides reliably every time, so I revise it afterward.

**My own contribution** — the architecture and every design decision above: proof-carrying definitions and the `∵` / `⟮⟯` notations, the `function_eval_auto` tactic and its three simp-attribute sets, the AC quarantine and its `#print axioms` enforcement, the function-as-set discipline, the chapter/section module layout, and the written [`proof_style.md`](proof_style.md), [`design_choices.md`](design_choices.md), and [`workflow.md`](workflow.md) that the whole development is held to. Also the review pass: revising drafted proofs to match the textbook's own argument, to use controlled `simp` over opaque automation, and to read as decomposed, stepwise proofs rather than dense terms.

---

## Quick Start

```bash
git clone https://github.com/Qinggao1729/axiomatic-set-theory
cd axiomatic-set-theory
lake exe cache get   # optional, speeds first build
lake build           # default target: the `Set` library
```

Requires Lean 4 via [elan](https://github.com/leanprover/elan); Lake ships with Lean.

## Repository Layout

| Path | Contents |
|---|---|
| `Set/Axioms.lean` | Primitive layer: `Set`, `∈`, `⊆`, ZF axioms, Infinity |
| `Set/Ch2/` | Axioms unpacked into constructions; arbitrary unions/intersections; algebra of sets |
| `Set/Ch3/` | Ordered pairs, relations, *n*-ary relations, functions, infinite products and AC, equivalence and quotients, orderings |
| `Set/Ch4/` | Inductive sets, the Infinity axiom in Enderton's form, `ω`, and induction on `ω` |
| `Set/Choice.lean` | Shared home for non-local AC forms |
| `Set/SimpAttrs.lean` | The three custom simp attributes |
| `Set/AxiomIndex.md` | Axiom → textbook page → declaration site |

## Further Reading

| Document | Purpose |
|---|---|
| [`TODO.md`](TODO.md) | Checklist mapping textbook statements to Lean declarations, with per-item proving status |
| [`design_choices.md`](design_choices.md) | Why the foundational choices were made: metalogic vs. object theory, shallow vs. deep embedding, `FunctionValue` unification costs |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | Module layout and the reasoning behind the AC structure |
| [`proof_style.md`](proof_style.md) | Proof conventions, tactic policy, naming and citation format |
| [`workflow.md`](workflow.md) | Per-section formalization procedure |
| [`PROJECT_GUIDE.md`](PROJECT_GUIDE.md) | Orientation for contributors |

