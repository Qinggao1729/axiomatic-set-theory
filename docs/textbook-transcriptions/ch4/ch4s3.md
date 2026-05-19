# Ch4 Section 3 (Recursion on \(\omega\)) - Textbook Extraction Draft

Source: Enderton, Chapter 4 "Recursion and the Isomorphism Theorem", pp. 73-79 in `Enderton_Textbook.pdf`.

This transcription tracks the set-theoretic development only: functions are relation graphs on sets, indices are elements of `ω`, and no Lean `Nat`/coding bridge is used.

## Narrative (book)

- **Recursion theorem on \(\omega\):** for \(a \in A\) and \(F : A \to A\), there exists a unique function \(h : \omega \to A\) with
  - \(h(0) = a\),
  - \(h(n^+) = F(h(n))\) for each \(n \in \omega\).
- **Theorem 4H:** every Peano system \(\langle N,S,e \rangle\) is isomorphic to \(\langle \omega,\sigma,0 \rangle\).

## Lean mapping (`Set/Ch4/S3_RecursionOnOmega.lean`)

Public (textbook-facing):

- `def RecursionSolution (h A a F : Set) : Prop := ...`
- `theorem recursion_exists_on_ω (A a F : Set) : a ∈ A → MapsInto F A A → ∃ h, RecursionSolution h A a F`
- `theorem recursion_solution_unique (A a F h₁ h₂ : Set) ... : h₁ = h₂`
- `theorem recursion_theorem_on_ω (A a F : Set) : a ∈ A → MapsInto F A A → ∃! h, RecursionSolution h A a F`
- `def IsPeanoIsomorphism (f N : Set) (S : Set → Set) (e : Set) : Prop := ...`
- `theorem thm_4H_peano_isomorphic (N : Set) (S : Set → Set) (e : Set) : IsPeanoSystem N S e → ∃ f, IsPeanoIsomorphism f N S e`

Internal proof scaffolding (kept `private` in the Lean file):

- segment predicate `IsRecursionSegment` and its existence/uniqueness chain,
- segment-to-global assembly via `recursionGraph`,
- local domain/range/functionality bridge lemmas used to close the recursion theorem proof.

## Proof-flow sketch in this repo

1. Build **partial recursion segments** on each `n ∈ ω` (`IsRecursionSegment`).
2. Prove existence and uniqueness of these segments by `ω`-induction.
3. Assemble the global recursion function as a relation graph (`recursionGraph`) by collecting segment values.
4. Derive existence and uniqueness of `RecursionSolution`.
5. For 4H, instantiate recursion with `GraphOn N S`, then prove onto/range-closure using the Peano induction axiom on `N`.

## Scope boundary

`S3` keeps the textbook recursion-and-isomorphism core only. Arithmetic-specific specializations (such as the successor graph used to define addition/multiplication recurrences) are kept in `Set/Ch4/S4_Arithmetic.lean`.

## Workflow note

After changing `Set/Ch4/S3_RecursionOnOmega.lean`, update `TODO.md` (Recursion on \(\omega\), Theorem 4H items) and keep this draft synchronized.
