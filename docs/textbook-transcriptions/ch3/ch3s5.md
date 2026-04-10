# Ch3 Section 5 (Infinite Cartesian Products) - Textbook Extraction Draft

Source: Enderton, Chapter 3, pp. 54-55.

## Core Definitions

1. Infinite Cartesian product over index set `I` and family `H`:
   - Set-theoretic form:
     - `∏_{i ∈ I} H(i) = { f | f is a function, dom(f)=I, and for every i∈I, f(i)∈H(i) }`.
   - In this repo (`Set`-as-family encoding):
     - `H` is a relation-like graph of index-to-fiber witnesses.
     - Value-membership condition is encoded by:
       - if `⟨i, y⟩ ∈ f`, then there exists `hi` with `⟨i, hi⟩ ∈ H` and `y ∈ hi`.

2. Axiom of Choice (second form):
   - If `H` is a function with domain `I` and each `H(i)` is nonempty, then a selector function exists.
   - Textbook consequence: the product `∏_{i∈I} H(i)` is nonempty.

## Formal Statements to Keep Aligned

- `noncomputable def InfiniteProduct (I H : Set) : Set := ...`
- `lemma InfiniteProduct.Spec {I H f : Set} : ...`
- `def ChoiceSecondForm : Prop := ...` (in `Set/Choice.lean`)
- `theorem infiniteProduct_nonempty_of_choice_second_form (hChoice₂ : ChoiceSecondForm) : ...`

## Proof Sketch: `ChoiceSecondForm -> (InfiniteProduct I H).Nonempty`

1. Use `ChoiceSecondForm` to obtain a selector relation `f` with:
   - `IsFunction f`
   - `dom f = I`
   - local selection property: each pair `⟨i,y⟩ ∈ f` picks from some fiber attached to `i` in `H`.
2. Show `f ∈ 𝒫 (I ⨯ ⋃ (ran H))`:
   - for `w ∈ f`, unpack `w = ⟨i,y⟩` via relation witness.
   - prove `i ∈ I` from `dom f = I`.
   - from selector property get `y ∈ hi` and `hi ∈ ran H`, so `y ∈ ⋃ (ran H)`.
   - conclude `⟨i,y⟩ ∈ I ⨯ ⋃ (ran H)` and thus `w` is in the product carrier.
3. Apply `InfiniteProduct.Spec` backward to conclude `f ∈ InfiniteProduct I H`.
4. Conclude nonemptiness by witness `f`.
