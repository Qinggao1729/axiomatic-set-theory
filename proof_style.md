# Proof Style Preferences

This file records preferred proof style choices for this project.

## Core Style

- Prefer readable, explicit proof structure in foundational files.
- Prefer named intermediate specifications, then finish with:
  - `simp only [named_spec_1, named_spec_2, ...]`
- Avoid heavy automation (`aesop`) in core theorem statements unless truly needed.
- `simp` / `simpa` / `simp_all` are allowed (and preferred) to collapse consecutive
  rewrites, including rewrites spread across hypotheses and goals.
- Avoid unnecessary `Classical`; use it deliberately when the mathematics is genuinely nonconstructive (especially AC-facing proofs).

## Core Summary (Quick version)

- Semantic steps explicit; routine logic handled by `simp`.
- Build a clear skeleton first (`intro` / `constructor` / `extensionality`).
- Prefer reusing previously proved theorems before re-proving logic manually.
- Use `exact` when a subgoal directly matches a hypothesis/projection.
- Use `rw` when the rewrite is simple and transparent.
- For multiple rewrites, prefer controlled simplification:
  use staged `simp only [...]` steps when that keeps intermediate states readable;
  use one big `simp`/`simp_all` pass only when it is clearly cleaner.
- For spec-heavy local goals, prefer `simp_all only [set_spec_simps]` instead of
  repeating long `rw [*.Spec]` chains.
- In branch-heavy uniqueness proofs, use `simp_all` proactively for equality substitution:
  even if goals are not closed immediately, normalize hypotheses first, then apply the key
  structural lemma (e.g. `Singleton.eq_pair`) on the simplified context.
- In branch cases, prefer short step-by-step closures (`apply` / `rw` / `exact`)
  over one complicated `exact` expression.
- Avoid long `exact (...)` expressions; prefer `refine`/`apply` to expose proof structure.
- Avoid complicated `exact (...)`, long `rw` chains, and unnecessary `have`.
- For intermediate steps, avoid both
  `have h : T := by exact ...` and `have h : T := (very long exact term ...)`.
  Prefer short direct assignment (`have h : T := ...`) or a small tactic block when needed.
- One-line declaration style is flexible (`:= by ...` vs direct term) when readability is clear.
- Use `aesop?` only to discover an idea, then rewrite the final proof cleanly.

## Agent Proof Protocol (MUST follow)

Before writing any new proof, do this checklist in order:

1. **Read this file first** (`proof_style.md`) before editing theorem proofs.
2. **Pick a visible skeleton first**:
   - equality of sets: `apply extensionality; intro x; constructor`
   - implication/subset: `intro ...`
   - iff goals: `constructor`
3. **Try theorem reuse before manual decomposition**:
   - look for already proved lemmas that match the current step (`*.mono`, `member_subset_*`, `*.Spec`, etc.)
   - prefer a short `rw` + `apply` chain using existing results over hand-written logical plumbing
   - if a repetitive micro-pattern appears in multiple branches, stop and factor it into a
     helper lemma first, then replace repeated blocks with that lemma
  - for nontrivial goals, explicitly ask first: "is this already proved in this file/chapter?"
    before opening definitions again
4. **If not immediately clear, write a 1-2 sentence human proof sketch first**:
   - identify the key reduction and which existing theorem should discharge it
   - then encode that sketch in Lean
5. **Immediately expose specs/definitions with `simp`**:
   - prefer `simp only [*.Spec, ...]` or `simp [*.Spec, ...]`
   - use `specialize` to instantiate `∀` hypotheses before simplifying
   - if you see many consecutive rewrites (possibly in assumptions + goal), replace them with one `simp`/`simpa`/`simp_all` step when clarity improves
6. **Keep logic manipulations lightweight**:
   - use `simp`/`simp only` for routine logical plumbing
   - if a subgoal is directly available, close it with `exact` (do not use `simpa` unnecessarily)
   - avoid long `exact (...)`; prefer `refine`/`apply` + short closures
   - avoid complicated `exact` terms (especially long nested terms or `fun ... => ...` inside `exact`)
   - in case branches, prefer short tactic steps (`apply`/`rw`/`exact`) to keep each step visible
7. **Use `rw` rarely**:
   - use `rw` when the rewrite is simple and transparent
   - avoid long or opaque `rw` chains when `simp` can do the routine work
   - if rewrites are repetitive across locations, prefer `simp only [...]` in small stages;
     use `simp`/`simp_all` in one shot only when it remains readable
8. **Use `have` sparingly**:
   - only for semantically meaningful intermediate facts, not routine rewrites
9. **If stuck**:
   - try `aesop?` as search only
   - then rewrite the final proof into explicit + `simp` style (do not keep opaque automation output)

10. **Respect namespace-level axiom boundaries**:
   - AC-dependent declarations should live in `namespace Choice` only when they truly invoke AC
   - AC-free declarations should stay in plain `namespace Set`
   - if a theorem can be proved without AC, do not place it in `Choice` just for convenience
   - when introducing a section where AC is used historically, `#check` AC declarations at the
     introduction point so usage is explicit in the file's narrative flow


Hard constraints for core files:

- Do not leave long nested function applications in final proof terms.
- Do not keep proof scripts that are mostly manual logical plumbing if `simp` can do it.
- "Simpler" means clearer structure and omission of unimportant micro-steps, not minimum line count.
- "Use `exact` when exact fits": if the goal is exactly a hypothesis/projection, use `exact` directly.
- Prefer
  `intro h; exact ...`
  over
  `exact (fun h => ...)`
  for contradiction/negation steps.

## Preferred Pattern for Uniqueness-Based Constructions

For objects built from an existence axiom (for example empty set, pair, power set):

1. Define canonical object (for example `Empty`, `Pair u v`, `Power A`).
2. Prove canonical spec lemma (`*.Spec`).
3. Prove an equality-by-spec lemma:
   - "Any set satisfying this same spec is equal to the canonical one."
   - Examples: `empty_eq_empty`, `pair_eq_pair`, `power_eq_power`.
4. Prove existence-and-uniqueness theorem:
   - Examples: `empty_unique`, `pair_unique`, `power_unique`.

## Conditional Definitions (Textbook-Hypothesis-Carrying)

When the textbook only defines an object *under a hypothesis* (e.g. Enderton
introduces `A / R` and the natural map only when `R` is an equivalence
relation on `A`), build the hypothesis into the `def` as a trailing
explicit proof argument, passed through the notation:

- `def QuotientSet (A R : Set) (_hEq : IsEquivalenceRelation R A) : Set := ...`
  with notation `A / R ∵ h` (`∵` reads "because"; it marks `h` as a proof,
  visually distinct from set-valued subscripts like `[x]₍R₎` and from the
  function-value `'(...)` symbol).
- No tactic discharge: the hypothesis is usually a named hypothesis in
  context, so it is simply written. By proof irrelevance the object does not
  depend on which proof is passed.
- Theorem statements mentioning such notation must bind the hypothesis
  *before* the colon (named binder, not `→`-form), so the name is in scope
  in the statement.
- In proofs, do not `rcases`/`obtain` away a hypothesis the goal depends on;
  copy it first and destructure the copy
  (`have hEq' := hEq; obtain ⟨...⟩ := hEq'`).
- Spec lemmas take the proof as an implicit binder appearing in the LHS
  pattern (e.g. `{hEq} : Q ∈ A / R ∵ hEq ↔ ...`), so `simp` unifies it with
  whatever proof occurs in the goal.
- Add an `app_unexpander` to print the notation (`A / R ∵ h`) instead of the
  kernel-style application.

## Readability Conventions

- Use semantic names for local equivalences:
  - `hAspec`, `hPspec`, `hSingletonSpec`, etc.
- Use semantic names for hypotheses:
  - `hxA`, `hxP`, `hySingleton`, etc.
- Prefer short, local transformations over tactic-heavy "magic."
- After destructuring an equation `h : a = X` where `a` is a local variable,
  prefer `subst h` over carrying the equation through `simpa [h]`/`calc`
  shuffling — it removes the variable and lets later steps be `exact`.
- Make a variable implicit when it is fully determined by the type of an
  explicit hypothesis argument (e.g. `{R A x y}` in Lemma 3N are forced by
  `hEq : IsEquivalenceRelation R A`, `hxA : x ∈ A`, `hyA : y ∈ A`).
- For theorem statements that are naturally membership equivalences, prefer
  textbook-style equational chains (`calc`):
  - e.g. `x ∈ ⋃(Pair A B) ↔ ... ↔ x ∈ A ∪ B`.
- Use `simp` for non-essential logical manipulations (re-association of `∃/∧/∨`,
  substitution by equalities, straightforward spec expansion), while keeping the
  conceptual structure explicit in named steps.
- For set equality theorems proved by membership equivalence, prefer this reusable skeleton:
  - `apply extensionality; intro x; constructor`
  - then keep the semantic step explicit (`*.Spec`) and let `simp` handle routine logic.
- Good default pattern for bridge theorems between two specs:
  - forward direction:
    - `simp only [Target.Spec]`
    - `simp [Source1.Spec, Source2.Spec] at hx`
    - `exact hx`
  - backward direction:
    - `simp only [Target.Spec] at hx`
    - `simp [Source1.Spec, Source2.Spec]`
    - `exact hx`
- When this pattern works cleanly, prefer it over long manual `rcases`/`cases` chains.

## Set-Theoretic Notation Summary

- **Core membership/subset:** `x ∈ A`, `x ∉ A`, `A ⊆ B`.
- **Basic sets/ops:** `∅`, `{x}`, `{x, y}`, `𝒫 A`, `A ∪ B`, `A ∩ B`, `A - B`.
- **Arbitrary unions/intersections:** `⋃A`, `⋂A`.
- **Ordered pairs and product:** `⟪x, y⟫` (preferred in section proofs), legacy alias `⟨x, y⟩`, and Cartesian product `A ⨯ B`.
- **Relation operators:** `dom R`, `ran R`, `fld R`.
- **Successor/naturals:** `a⁺`, `ω`, `zero_ω`, `one_ω`.
- **Function-style relation operators:** `F⁻¹`, `F ∘ G`, `F ↾ C`, `F⟦C⟧`.
- **Quotient/equivalence notation:** `[x]₍R₎`, `A / R ∵ h` (where `h : IsEquivalenceRelation R A`).
- **Chapter 5 numeric carriers:** `ℤ`, `ℤ'`, `ℚ`, `ℝ` and their operations (`+_ℤ`, `·_ℤ`, `<_ℤ`, etc.).

## Textbook Citation Comment Format

- For every declaration (`def`/`theorem`/`lemma`/`axiom`/`abbrev`) that corresponds to a
  textbook definition/theorem/lemma/corollary, place a Lean **doc-comment** (`/-- ... -/`,
  not `/- ... -/`) immediately above the declaration, in this exact form:
  - `/-- [Enderton ChN §M, p.PP] "literal textbook wording." -/`
  - The bracket is `[Enderton Ch<chapter> §<section>, p.<page-or-range>]`
    (e.g. `[Enderton Ch3 §7, p.62]`, `[Enderton Ch4 §1, pp.68-69]`).
  - Follow the bracket with the relevant textbook statement quoted **literally** in double
    quotes. Use backtick code spans for symbols inside the prose where it aids readability.
- Exemplars (study these for the exact look): `Set/Ch3/S7_OrderingRelations.lean`,
  `Set/Ch4/S1_InductiveSets.lean`.
- After the literal quote, a short clarifying sentence is allowed (e.g. to record a
  deviation, a defined-here-because note, or the proof idea when the book gives none), but
  keep the literal quote first.
- For a derived helper / component of a numbered result (not a standalone numbered theorem),
  still cite the parent result and pages, e.g.
  `/-- [Enderton Ch4 §4, pp.82-83] "Theorem 4K (commutativity of addition)" ... -/`.

## Numbered Declaration Naming

- If a declaration corresponds to an explicitly numbered Enderton result, the primary
  declaration name should start with that number label.
- Preferred short prefixes for numbered declarations:
  - theorem: `thm_<number>_<name>`
  - lemma: `lem_<number>_<name>`
  - corollary: `cor_<number>_<name>`
  - axiom: `ax_<number>_<name>`
  - Examples: `thm_3E_domain_inverse`, `lem_4La_natural_succ_mem_iff`,
    `cor_4P_add_right_cancel`, `ax_2A_no_universal_set`.
- Number token formatting:
  - keep chapter/theorem letters (for example `3E`, `4K`, `5QF`);
  - attach a parenthesized sub-label directly to the number token with no separator
    (for example `4L(a)` -> `4La`, `3K(b)` -> `3Kb`, `3J(a)` -> `3Ja`).
- Use this rule only when the numbering is explicitly known from the source/comment.
  Do not guess theorem numbers.
- For high-churn foundational names used widely across chapters, temporary compatibility
  aliases are acceptable during refactors; after migration, new references should prefer
  the short numbered primary declaration.

## Simp Usage

- `Spec` vs `Spec_full` convention for comprehension-based objects:
  - If a definition is `Comprehension P carrier`, prefer:
    - `*.Spec_full`: includes the carrier conjunct (e.g. `x ∈ carrier ∧ ...`).
    - `*.Spec`: drops the carrier conjunct and keeps the semantic part used in
      most proofs.
  - Keep `*.Spec` as the default lemma for rewriting and simp usage; use
    `*.Spec_full` only when a proof explicitly needs carrier membership.
  - Naming should mirror existing style:
    `Product.Spec_full` / `Product.Spec`,
    `InfiniteProduct.Spec_full` / `InfiniteProduct.Spec`.

- Good candidates for `@[simp]`:
  - canonical spec lemmas like `Empty.Spec`, `Pair.Spec`, `Singleton.Spec`, `Power.Spec`.
- Use the custom simp set `set_spec_simps` to accumulate `*.Spec` lemmas and simplify
  spec expansions consistently (`simp only [set_spec_simps]`, `simp_all only [set_spec_simps]`).
- For `f(x)` side-condition automation (`IsFunction f`, `x ∈ dom f`), place only
  relevant non-`*.Spec` bridge lemmas in `function_eval_sideconds`, and run
  `simp_all [function_eval_sideconds]` first, then
  `simp_all [set_spec_simps, function_eval_sideconds]`; if these fail, fall back to
  controlled `simp_all only [...]` with `prop_simps` for core propositional
  rewrites.
- Use `function_eval_auto` for routine discharge of these side conditions; use
  `function_eval_auto?` when you want `simp?`-style suggestion logs first.
- If repeated `F⟮x⟯` use leads to `maxHeartbeats` timeouts, see the section
  "`F⟮x⟯` / `FunctionValue` unification timeouts" below.
- Avoid `@[simp]` on uniqueness theorems (`*_unique`) or large conditional equality lemmas by default.
- Also avoid `@[simp]` on bridge/equivalence theorems like
  `bigUnion_pair` / `bigIntersection_pair` by default:
  - these are useful rewrite facts, but not canonical simplification rules.
  - keep them as ordinary theorems and invoke them explicitly (`rw`/`simp [theorem]`) when needed.
- Prefer `@[simp]` for canonical membership specifications (`*.Spec`) and similar
  definitional normal forms; avoid promoting algebraic laws (e.g. commutativity/associativity)
  to global simp rules unless there is a strong, local justification.

## `F⟮x⟯` / `FunctionValue` unification timeouts

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

## Implementation Preferences (Core Files)

- Prefer `simp`/`simp only` for simple logical manipulations and spec/definition unfolding.
  - "Simple" includes routine transformations of `∧`, `∨`, `∃`, and straightforward substitutions.
- Use `rw` rarely; prefer `simp` when the step is just rewriting/spec expansion.
- Use `rw` directly when it is the clearest one-step rewrite (do not avoid `rw` dogmatically).
- When there are consecutive `rw` steps (especially mixed across hypotheses/goals),
  prefer one clear `simp`/`simpa`/`simp_all` step instead.
- For primitive notations, prefer direct forms that do not introduce extra wrapper layers
  in day-to-day proofs (for example keep `∉` as direct function-style notation) unless there is a
  concrete metaprogramming reason to introduce a named wrapper.
- For ordered tuples/pairs in section code from `Set/Ch3/S4_Functions.lean` onward, prefer
  `⟪x, y⟫` notation over `⟨x, y⟩` so ordered pairs are visually distinct from Lean constructor
  tuples used for `∧`/`∃` witnesses.
- Avoid frequent `have` blocks when the same effect can be achieved inline by `simp`/`simpa`.
- Avoid long nested function applications and deeply nested tactical blocks.
- Prefer plain `exact` for direct closures; do not wrap direct closures in `simpa`.
- For branch-specific goals, avoid large one-line terms; split into 2-3 clear steps
  (`apply` then `rw`, then `exact`) when that improves readability.
- In uniqueness/case-heavy proofs, it is good style to:
  - run `simp_all` to push equalities through the local context first,
  - then apply one semantic helper lemma (for example `Singleton.eq_pair`,
    `Pair.eq_pair_left_or`, `Pair.eq_pair_right_or`) instead of redoing membership plumbing.
- In proof search order, prefer:
  - existing theorem reuse (`apply`/`exact`/`rw [known theorem]`)
  - then `simp` for routine logic
  - manual decomposition only if necessary.
- "Simplifying a proof" means:
  - omit unimportant intermediate steps,
  - keep conceptual steps visible,
  - not necessarily fewer lines.
- If stuck, `aesop?` is acceptable as a search aid, but then rewrite the final proof in a cleaner style
  (usually `simp` + explicit core steps) instead of keeping the full automation output.
