# Proof Style Preferences

This file records preferred proof style choices for this project.

## Core Style

- Prefer readable, explicit proof structure in foundational files.
- Prefer named intermediate specifications, then finish with:
  - `simp only [named_spec_1, named_spec_2, ...]`
- Avoid heavy automation (`aesop`) in core theorem statements unless truly needed.
- `simp` / `simpa` / `simp_all` are allowed (and preferred) to collapse consecutive
  rewrites, including rewrites spread across hypotheses and goals.
- Try not to use `Classical`

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

## Readability Conventions

- Use semantic names for local equivalences:
  - `hAspec`, `hPspec`, `hSingletonSpec`, etc.
- Use semantic names for hypotheses:
  - `hxA`, `hxP`, `hySingleton`, etc.
- Prefer short, local transformations over tactic-heavy "magic."
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

## Simp Usage

- Good candidates for `@[simp]`:
  - canonical spec lemmas like `Empty.Spec`, `Pair.Spec`, `Singleton.Spec`, `Power.Spec`.
- Use the custom simp set `set_spec_simps` to accumulate `*.Spec` lemmas and simplify
  spec expansions consistently (`simp only [set_spec_simps]`, `simp_all only [set_spec_simps]`).
- Avoid `@[simp]` on uniqueness theorems (`*_unique`) or large conditional equality lemmas by default.
- Also avoid `@[simp]` on bridge/equivalence theorems like
  `bigUnion_pair` / `bigIntersection_pair` by default:
  - these are useful rewrite facts, but not canonical simplification rules.
  - keep them as ordinary theorems and invoke them explicitly (`rw`/`simp [theorem]`) when needed.

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
