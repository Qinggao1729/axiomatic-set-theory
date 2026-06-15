# Project guide: axiomatic set theory in Lean 4

This document is for anyone who wants to **clone the repo, understand the layout, and contribute** without prior context on this codebase.

---

## 1. What this project is

- **Goal:** Formalize set theory along **Herbert B. Enderton**, *Elements of Set Theory*, in **Lean 4**.
- **Style:** A primitive type `Set`, membership `∈`, and **axioms** close to Enderton’s development (extensionality, empty set, pairing, unions, power set, comprehension, infinity, etc.). On top of that, definitions and theorems are built chapter-by-chapter.
- **Textbook:** *Elements of Set Theory* (Enderton). Keep a **local PDF** if you use one (the standard filename is gitignored as copyrighted material); `docs/textbook-transcriptions/` and the Lean files should still follow the book’s statements and order.
- **Lineage:** Some early direction was informed by prior public Lean work 
(see [ACKNOWLEDGMENTS.md](ACKNOWLEDGMENTS.md)); this repository’s layout, 
proofs, and workflow are maintained here independently.

---

## 2. Prerequisites

- **Lean 4** via [elan](https://github.com/leanprover/elan) (the repo pins a version in `lean-toolchain`).
- **Lake** (ships with Lean) for builds.
- Familiarity with **tactic mode** proofs and basic Mathlib usage helps; the project is mostly custom set theory, not heavy Mathlib algebra.

**First-time setup**

```bash
cd axiomatic-set-theory
lake exe cache get   # optional but speeds first Mathlib build
lake build
```

Default library target is **`Set`** (see `lakefile.toml`). A full `lake build` typechecks the whole project.

---

## 3. Repository layout (what to open first)

| Path | Role |
|------|------|
| `Set.lean` | **Root import:** pulls in `Set.Axioms` and aggregators `Set.Ch2`, `Set.Ch3`, `Set.Ch4`. |
| `Set/Axioms.lean` | **Primitive layer:** `Set`, `∈`, `⊆`, and **Ch2 axioms** (extensionality, empty, pairing, union, power, comprehension), plus the primitive witness-form Infinity axiom. |
| `Set/Ch2/` | Chapter 2: axioms unpacked into definitions, `Comprehension`, unions/intersections, algebra of sets. |
| `Set/Ch3/` | Chapter 3: ordered pairs, relations, n-ary relations, functions, choice-related products, equivalence, orderings. |
| `Set/Ch4/` | Chapter 4: inductive sets, the Infinity axiom, `ω`, and induction on `ω` (S1; later sections planned). |
| `Set/Ch2.lean`, `Ch3.lean`, … | **Chapter aggregators** — each re-exports that chapter’s section files in order. |
| `Set/Choice.lean` | Single home for the (six) equivalent forms of AC under the `Set.Choice` sub-namespace. Imported from `Set/Ch3/S4_Functions.lean` (Theorem 3J) and `Set/Ch3/S5_InfiniteCartesianProducts.lean` (infinite products). AC predicates state "function" inline so this file only depends on `Set.Ch3.S2_Relations`, breaking what would otherwise be a circular dependency. |
| `Set/SimpAttrs.lean` | Custom simp attribute `set_spec_simps` for membership specification lemmas. |

**Legacy / shim**

- `Set/Basic.lean` is a thin compatibility import; most real content lives under `Set/Ch2/…`.
- Other top-level files under `Set/` (e.g. older monolithic modules) may exist for history; **prefer the `Set/Ch*/S*.lean` tree** when adding material.

---

## 4. Design patterns (how the mathematics is encoded)

### 4.1 Axioms vs definitions

- **Axioms** live in `Set/Axioms.lean` as existential statements (e.g. “there exists a set `B` such that …”).
- **Named sets** (empty, pair, comprehension instance, etc.) are usually **`noncomputable def`**s built with `Classical.choose` on the axiom, plus a **`*.Spec`** lemma from `Classical.choose_spec` (or, for comprehension-shaped objects, via `Comprehension` and `Comprehension.Spec` in `Set/Ch2/S1_Axioms.lean`).

### 4.2 The `Comprehension` wrapper

Many constructions that are “subset of a carrier defined by a predicate” use:

- `noncomputable def Comprehension (P : Set → Prop) (c : Set) : Set := Classical.choose (comprehension P c)`
- `lemma Comprehension.Spec : x ∈ Comprehension P c ↔ x ∈ c ∧ P x`

Prefer **reusing `Comprehension`** instead of repeating `Classical.choose (comprehension …)` at every call site; proofs then `simp` with `Comprehension.Spec`.

### 4.3 `*.Spec` lemmas

- For each important defined set, there is typically a lemma **`Name.Spec`** giving **membership** `x ∈ Name … ↔ …`.
- Many are tagged with `attribute [set_spec_simps] Name.Spec` so you can write `simp only [set_spec_simps]` or `simp_all only [set_spec_simps]` instead of long rewrite chains.
- **Implicit arguments:** `*.Spec` lemmas often use **implicit** parameters; call them as `Foo.Spec` and only add `(x := …)` when Lean cannot infer (see project norms in Cursor rules).

### 4.4 Notation

Examples (exact names vary by file): `∅`, `𝒫`, `⋃`, `⋂`, ordered pairs `⟪x, y⟫` or `⟨x, y⟩`, `dom` / `ran`, successor `⁺`, `ω`, etc. Hover in the editor or search for `notation` / `infix` in the relevant section file.

---

## 5. How we work on a new section (mandatory process)

Read **`workflow.md`** end-to-end. Short summary:

1. **Read the textbook** section (local PDF or `docs/textbook-transcriptions/`).
2. **Draft a transcription** under `docs/textbook-transcriptions/` (e.g. `docs/textbook-transcriptions/ch4/ch4s2.md`, `ch4/ch4s3.md`): statements, proof sketches, mapping to Lean names.
3. **Update `TODO.md`** *before* or in lockstep with proofs: checkbox items with **Set theory** and **Lean** lines, concrete declaration names, primary `.lean` path.
4. **Implement** in the matching `Set/Ch#/S*.lean` file: definitions → `*.Spec` → theorems in book order when possible.
5. **Verify** with `lake build` (and fix lints on touched files).

Synchronization rule: **TODO section and the corresponding Lean file must agree** (no checked items without code, no major theorems missing from the TODO).

---

## 6. Proof style

Read **`proof_style.md`** before writing or refactoring proofs. In short:

- Prefer a **visible skeleton** (`extensionality`, `constructor`, `intro`).
- Prefer **`simp` / `simp_all`** with `set_spec_simps` for routine membership reasoning.
- Avoid opaque automation in finished proofs; **`aesop?` is for discovery**, then rewrite by hand.
- The repo has Cursor rules (e.g. under `.cursor/rules/`) that reinforce textbook-first and TODO/style updates.

---

## 7. Editor and AI assistance

- **Lean 4 extension** for VS Code / Cursor is strongly recommended.
- Workspace rules may tell agents to consult the **textbook**, **`workflow.md`**, **`proof_style.md`**, and **`TODO.md`** when formalizing.

---

## 8. Common tasks (cheat sheet)

| Task | Command / action |
|------|------------------|
| Full build | `lake build` |
| After changing imports | Rebuild; if the IDE says imports are stale, use “Restart File” / restart Lean server |
| Find a definition | ripgrep symbol name in `Set/` or use Lean “Go to definition” |
| Add a section | New file `Set/Ch#/S*_*.lean`, import it from `Set/Ch#.lean` in order, then update TODO + transcription |

---

## 9. Known limitations / honesty

- **Later chapters** (Chapter 4 Section 2 onward, and Chapter 5) are planned but not yet present in the repository.
- The primitive **infinity axiom** is declared in `Set/Axioms.lean`; `Set/Ch4/S1_InductiveSets.lean` derives Enderton's literal form as `theorem infinity_inductive : ∃ A, Inductive A`. The chosen witness is `noncomputable def Infinity := Classical.choose infinity_inductive`, with spec `lemma Infinity.Inductive`, mirroring the `Empty`/`Pair`/`Power`/… pattern from `Set/Ch2/S1_Axioms.lean`.

---

## 10. Where to read next

| Document | Purpose |
|----------|---------|
| `README.md` | High-level mathematical overview (some code snippets may lag refactors; trust the `.lean` files). |
| `workflow.md` | Per-section formalization procedure. |
| `proof_style.md` | Proof conventions and tactics. |
| `TODO.md` | Planning checklist (Chapters 2–5). |
| `docs/textbook-transcriptions/` | Section-by-section extractions from the book. |
| `ARCHITECTURE.md` | Chapter/section module layout (`Set/Ch*/S*.lean`). |

Once you have run `lake build` successfully and located the chapter you care about under `Set/Ch#/`, you are ready to make a focused change: **one section at a time**, **textbook + TODO + transcription + Lean + build**.
