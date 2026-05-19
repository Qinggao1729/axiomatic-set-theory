# Ch4 Section 4 (Arithmetic) - Textbook Extraction Draft

Source: Enderton, Chapter 4 "Arithmetic", pp. 79-83 in `Enderton_Textbook.pdf`.

This section stays in the set-theoretic universe: numbers are elements of `ω`, and
operations are relation-graphs/function-graphs on sets (no Lean `Nat` bridge).

## Narrative (book)

- Define addition on `ω` by recursion in the second argument:
  - `m + 0 = m`
  - `m + n^+ = (m + n)^+`
- Define multiplication on `ω` by recursion:
  - `m · 0 = 0`
  - `m · n^+ = (m · n) + m`
- Define exponentiation by recursion:
  - `m^0 = 1`
  - `m^(n^+) = (m^n) · m`
- Prove the basic arithmetic laws (4K): associativity/commutativity and distributive laws.

## Lean mapping (`Set/Ch4/S4_Arithmetic.lean`)

Public (textbook-facing):

- `def IsBinaryOperationOn (A op : Set) : Prop := ...`
- `noncomputable def NatAdd (m n : Set) : Set`
- `theorem nat_add_zero (m : Set) : m ∈ ω → m + zero_ω = m`
- `theorem nat_add_succ (m n : Set) : m ∈ ω → n ∈ ω → m + n⁺ = (m + n)⁺`
- `noncomputable def NatMul (m n : Set) : Set`
- `theorem nat_mul_zero (m : Set) : m ∈ ω → m * zero_ω = zero_ω`
- `theorem nat_mul_succ (m n : Set) : m ∈ ω → n ∈ ω → m * n⁺ = (m * n) + m`
- `noncomputable def NatPow (m n : Set) : Set`
- `theorem nat_pow_zero (m : Set) : m ∈ ω → m ^ zero_ω = one_ω`
- `theorem nat_pow_succ (m n : Set) : m ∈ ω → n ∈ ω → m ^ (n⁺) = (m ^ n) * m`
- `theorem thm_4K_basic_arithmetic_laws : ...`

Internals:

- The file uses private recursion wrappers and private graph/canonical-value lemmas to build
  the operations cleanly while keeping the public surface focused on textbook statements.
- Additional public closure/bridge lemmas (`nat_add_closed`, `nat_mul_closed`, `nat_pow_closed`,
  `nat_zero_add`, `nat_succ_add`, `nat_zero_mul`, `nat_mul_succ_left`, etc.) are retained
  because they are reused by later chapter files.

## Proof-flow sketch in this repo

1. Build each operation from recursion theorem on `ω` (in `S3`) via set-valued relation graphs.
2. Extract unique values at each index from function-graph uniqueness.
3. Prove base/step equations (`4I`, `4J`, exponentiation characterization).
4. Derive algebraic laws (`4K`) by induction plus already-proved recursion equations.

## Workflow note

After changing `Set/Ch4/S4_Arithmetic.lean`, keep this draft and the arithmetic section in
`TODO.md` synchronized.
