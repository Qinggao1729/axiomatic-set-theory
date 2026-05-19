# Ch4 Section 2 (Peano's Postulates) - Textbook Extraction Draft

Source: Enderton, Chapter 4 "Peano's Postulates" and transitive-set material, pp. 70–73 in `Enderton_Textbook.pdf`.

## Narrative (book)

- Peano system: triple `⟨N, S, e⟩` with `S : N → N`, `e ∈ N`, `e ∉ ran S`, `S` one-to-one, and Peano induction (any subset of `N` containing `e` and closed under `S` equals `N`).
- **Theorem 4D:** `⟨ω, σ, 0⟩` is a Peano system, where `σ` is successor restricted to `ω` (in Lean we use `fun n => n⁺` on `ω`).
- **Definition (transitive set):** `x ∈ a ∈ A ⇒ x ∈ A` (and equivalent forms `⋃A ⊆ A`, etc.).
- **Theorem 4E:** If `a` is transitive, then `⋃(a⁺) = a`.
- **Theorem 4F:** Every natural number is a transitive set (proof by induction on `ω`).
- **Theorem 4G:** `ω` is a transitive set.

## Lean encoding note

Enderton states Peano postulates with `S` as a function `N → N`. This repo encodes that as a set-level map `S : Set → Set`, with quantification restricted by membership in `N`:

- `e ∈ N`, `∀ n ∈ N, S n ∈ N`, `∀ n ∈ N, S n ≠ e`, injectivity of `S` on `N`, and the subset induction principle.

This matches the book’s content; `e ∉ ran S` is expressed as “no successor hits `e`,” and the development stays in the `Set` universe (no Lean `Nat` layer).

## Mapping to Lean (`Set/Ch4/S2_PeanosPostulates.lean`)

| Book | Lean |
|------|------|
| Transitive set | `def IsTransitiveSet (A : Set) : Prop := ∀ x a, x ∈ a → a ∈ A → x ∈ A` |
| Peano system (encoded) | `def IsPeanoSystem (N : Set) (S : Set → Set) (e : Set) : Prop := ...` |
| Helper: `a⁺ ≠ ∅` | `lemma successor_ne_empty (a : Set) : a⁺ ≠ ∅` |
| Theorem 4E | `theorem bigunion_successor_of_transitive (a : Set) : IsTransitiveSet a → ⋃(a⁺) = a` |
| Theorem 4F | `theorem natural_transitive_set (n : Set) : Natural n → IsTransitiveSet n` |
| Theorem 4G | `theorem ω_transitive_set : IsTransitiveSet ω` |
| Theorem 4D | `theorem omega_peano_system : IsPeanoSystem ω (fun n => n⁺) ∅` |

### Implementation auxiliaries (used in later sections)

The file also includes two set-theoretic bridge lemmas reused by Ch4S3/Ch4S5:

- `theorem natural_not_mem_self (n : Set) : n ∈ ω → n ∉ n`
- `theorem succ_mem_succ_of_mem (m n : Set) : n ∈ ω → m ∈ n → m⁺ ∈ n⁺`

## Proof-flow sketches

- **4D:** `0 ∈ ω` and successor closure from `ω` inductive; `n⁺ ≠ 0` via `successor_ne_empty`; injectivity of successor on `ω` via 4F + 4E and `⋃(m⁺) = m`; induction postulate from minimality of `ω` (`thm_4B_ω_subset_of_inductive`).
- **4E:** Expand `a⁺ = a ∪ {a}`; `⋃(a⁺) = ⋃a ∪ ⋃{a} = ⋃a ∪ a`; for transitive `a`, `⋃a ⊆ a`, hence union is `a`.
- **4F:** `T = { n ∈ ω | n transitive }`; show `T` inductive; conclude `T = ω` in spirit via `Natural`.
- **4G:** `T = { n ∈ ω | n ⊆ ω }`; inductive; every `a ∈ ω` has `a ⊆ ω`, hence transitivity of membership.
