# Ch3 Section 4 (Functions) — Textbook Extraction

Source: Enderton, *Elements of Set Theory*, Chapter 3 "Relations and Functions",
"Functions" subsection, pp. 42–54 (`Enderton_Textbook.pdf`).

This transcription tracks the set-theoretic content used to formalize the
section in `Set/Ch3/S4_Functions.lean`. Theorem statements are reproduced
verbatim (with light typographic normalization); proofs are sketched in the
order Enderton gives them. Cross-file links are mentioned where the textbook
content is split between this section and a neighbouring one.

## 1. Definitions (pp. 42–45)

- **Function.** A function is a relation `F` such that for each `x ∈ dom F`
  there is only one `y` such that `xFy`.
- For a function `F` and `x ∈ dom F`, the unique `y` with `xFy` is the value
  of `F` at `x`, written `F(x)`. (Enderton resolves to use `F(x)` only when
  `F` is a function and `x ∈ dom F`.)
- **Maps into / onto.** `F : A → B` iff `F` is a function, `dom F = A`,
  and `ran F ⊆ B`. `F` maps `A` onto `B` if additionally `ran F = B`.
- **Single-rooted / one-to-one.** A set `R` is *single-rooted* iff for each
  `y ∈ ran R` there is only one `x` with `xRy`. A function is one-to-one
  iff it is single-rooted.
- **Operations on relations.**
  - Inverse: `F⁻¹ = {⟨u, v⟩ | vFu}`
  - Composition: `F ∘ G = {⟨u, v⟩ | ∃ t (uGt ∧ tFv)}`
  - Restriction: `F ↾ A = {⟨u, v⟩ ∈ F | u ∈ A}`
  - Image: `F[A] = ran(F ↾ A) = {v | ∃ u ∈ A, uFv}`. When `F` is a function
    and `A ⊆ dom F`, also `F[A] = {F(u) | u ∈ A}`.

## 2. Theorems 3E–3I (pp. 45–47)

These theorems are already transcribed in earlier project notes; we restate
them only briefly for reference.

- **Theorem 3E.** For any set `F`: `dom(F⁻¹) = ran F` and `ran(F⁻¹) = dom F`.
  For a relation `F`: `(F⁻¹)⁻¹ = F`.
- **Theorem 3F.** For any set `F`: `F⁻¹` is a function iff `F` is single-rooted.
  Dually, a relation `F` is a function iff `F⁻¹` is single-rooted.
- **Theorem 3G.** If `F` is one-to-one, then for `x ∈ dom F` we have
  `F⁻¹(F(x)) = x`, and for `y ∈ ran F` we have `F(F⁻¹(y)) = y`.
- **Theorem 3H.** If `F` and `G` are functions, then `F ∘ G` is a function,
  with `dom(F ∘ G) = {x ∈ dom G | G(x) ∈ dom F}` and
  `(F ∘ G)(x) = F(G(x))` for every `x ∈ dom(F ∘ G)`.
- **Theorem 3I.** `(F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹` for arbitrary sets `F`, `G`.

## 3. Theorem 3J — left/right inverses (pp. 48–49)

> **Theorem 3J.** Assume that `F : A → B`, and that `A` is nonempty.
>
> **(a)** There exists a function `G : B → A` (a "left inverse") such that
> `G ∘ F` is the identity function `I_A` on `A` iff `F` is one-to-one.
>
> **(b)** There exists a function `H : B → A` (a "right inverse") such that
> `F ∘ H` is the identity function `I_B` on `B` iff `F` maps `A` onto `B`.

**Proof (Enderton).**

- *(a, ⇐)* Assume `G ∘ F = I_A`. If `F(x) = F(y)`, apply `G` to both sides:
  `x = G(F(x)) = G(F(y)) = y`, so `F` is one-to-one.
- *(a, ⇒)* Assume `F` is one-to-one. Then `F⁻¹` is a function from `ran F`
  onto `A` (Theorems 3E and 3F). Pick a fixed `a ∈ A` and extend `F⁻¹` to
  all of `B` by sending every point of `B - ran F` to `a`:
  $$
    G(x) = \begin{cases} F^{-1}(x) & \text{if } x \in \mathrm{ran}\, F,\\
                         a          & \text{if } x \in B - \mathrm{ran}\, F. \end{cases}
  $$
  In one line, `G = F⁻¹ ∪ (B - ran F) × {a}` (see Fig. 10(a)). This `G`
  maps `B → A`, has `dom(G ∘ F) = A`, and `G(F(x)) = F⁻¹(F(x)) = x` for
  every `x ∈ A`, so `G ∘ F = I_A`. **No AC is used:** the extension is
  completely determined by the choice of `a`.
- *(b, ⇐)* Assume `F ∘ H = I_B`. For any `y ∈ B`, `y = F(H(y))`, so
  `y ∈ ran F`. Therefore `ran F = B`, i.e. `F` is onto.
- *(b, ⇒)* Assume `F` maps `A` onto `B`. We cannot just take `H = F⁻¹`
  because `F` is in general not one-to-one and `F⁻¹` is then not a
  function. For each `y ∈ B` we *must choose* some `x` with `F(x) = y`
  and let `H(y)` be that chosen `x` (see Fig. 10(b)). The existence of
  such an `x` is guaranteed by `ran F = B`, but selecting one for every
  `y` simultaneously requires the Axiom of Choice.

> **Axiom of Choice (first form).** For any relation `R` there is a
> function `H ⊆ R` with `dom H = dom R`.

With this axiom, taking `H ⊆ F⁻¹` with `dom H = dom F⁻¹ = ran F = B`
gives the right inverse: for any `y ∈ B`, `⟨y, H(y)⟩ ∈ F⁻¹`, hence
`⟨H(y), y⟩ ∈ F`, hence `F(H(y)) = y`.

**Figure 10 (transcription).**

- (a) `G` extends `F⁻¹` by collapsing the "leftover" elements
  `B - ran F` to the fixed witness `a ∈ A`. The diagram shows `B`
  partitioned into `ran F` and `B - ran F`, with horizontal arrows
  carrying `ran F` back to `A` via `F⁻¹` and all of `B - ran F` to the
  same point `a ∈ A`.
- (b) `H` selects, for each `y ∈ B`, one preimage from the (possibly
  many) `x`'s satisfying `F(x) = y`. The diagram shows three preimages
  `x', x'', H(y) = x` of a single `y`, with `H` picking the one labelled
  `H(y) = x`.

## 4. Theorem 3K — image and set operations (pp. 50–51)

> **Theorem 3K.** The following hold for any sets. (`F` need not be a function.)
>
> **(a)** The image of a union is the union of the images:
>
> $$F[A \cup B] = F[A] \cup F[B] \qquad \text{and} \qquad F\bigl[\textstyle\bigcup \mathscr{A}\bigr] = \bigcup\{F[A] \mid A \in \mathscr{A}\}.$$
>
> **(b)** The image of an intersection is included in the intersection of the images:
>
> $$F[A \cap B] \subseteq F[A] \cap F[B] \qquad \text{and} \qquad F\bigl[\textstyle\bigcap \mathscr{A}\bigr] \subseteq \bigcap\{F[A] \mid A \in \mathscr{A}\}$$
>
> for nonempty `𝒜`. **Equality holds if `F` is single-rooted.**
>
> **(c)** The image of a difference includes the difference of the images:
>
> $$F[A] - F[B] \subseteq F[A - B].$$
>
> **Equality holds if `F` is single-rooted.**

**Example (Enderton).** `F : ℝ → ℝ`, `F(x) = x²`, `A = [-2, 0]`, `B = [1, 2]`.
Then `F[A] = [0, 4]`, `F[B] = [1, 4]`, so

- `F[A ∩ B] = F[∅] = ∅`, but `F[A] ∩ F[B] = [1, 4]`,
- `F[A] - F[B] = [0, 1)`, but `F[A - B] = F[A] = [0, 4]`.

This example shows that the subsets in (b) and (c) are in general strict.

**Proof (Enderton).**
- Part (a), binary form, is a direct membership calculation:
  `y ∈ F[A ∪ B] ↔ (∃ x ∈ A ∪ B) xFy ↔ (∃ x ∈ A) xFy ∨ (∃ x ∈ B) xFy ↔ y ∈ F[A] ∨ y ∈ F[B]`.
- Part (b), binary form, follows from the same calculation up to the middle
  step `(∃ x ∈ A ∩ B) xFy ⇒ (∃ x ∈ A) xFy ∧ (∃ x ∈ B) xFy`, which is not in
  general reversible. If `F` is single-rooted, the two witnesses `x₁, x₂`
  collapse to a common `x ∈ A ∩ B`, so equality holds.
- Part (c) is the calculation
  `y ∈ F[A] - F[B] ↔ (∃ x ∈ A) xFy ∧ ¬ (∃ t ∈ B) tFy ⇒ (∃ x ∈ A - B) xFy ↔ y ∈ F[A - B]`.
  Again single-rootedness reverses the middle step.
- The arbitrary forms generalize the binary ones along the same outline;
  Enderton defers their details to Exercise 26.

**Remark.** The second halves of (a) and (b) require speaking of the set
`{F[A] | A ∈ 𝒜}`, i.e. the image-family of `𝒜` under `F`. We formalize this
explicitly as `ImageFamily F 𝒜` in the Lean development (see §6 below).

## 5. Corollary 3L — inverse image is well-behaved (p. 51)

> **Corollary 3L.** For any function `G` and sets `A`, `B`, and `𝒜`:
>
> $$G^{-1}\bigl[\textstyle\bigcup \mathscr{A}\bigr] = \bigcup\{G^{-1}[A] \mid A \in \mathscr{A}\},$$
> $$G^{-1}\bigl[\textstyle\bigcap \mathscr{A}\bigr] = \bigcap\{G^{-1}[A] \mid A \in \mathscr{A}\} \qquad \text{for } \mathscr{A} \neq \varnothing,$$
> $$G^{-1}[A - B] = G^{-1}[A] - G^{-1}[B].$$

**Justification (Enderton, narrative).** The inverse of a function is always
single-rooted (Theorem 3F applied to `G`); the three equalities are then the
equality cases of Theorem 3K specialized to `G⁻¹`.

> Note. Enderton's 3L only mentions the *arbitrary* union and intersection
> equalities together with the *binary* difference equality. The
> corresponding *binary* union/intersection equalities for `G⁻¹` follow as
> immediate corollaries (and have been recorded separately as
> `inverse_image_union`, `inverse_image_inter`, `inverse_image_diff`).

## 6. Indexed families and function space (pp. 51–52)

After 3L, Enderton introduces convenience notation. Let `I` be a set and
`F` a function whose domain includes `I`. Define

$$\bigcup_{i \in I} F(i) = \bigcup \{F(i) \mid i \in I\} = \{x \mid x \in F(i) \text{ for some } i \in I\}$$

and, for `I ≠ ∅`,

$$\bigcap_{i \in I} F(i) = \bigcap \{F(i) \mid i \in I\} = \{x \mid x \in F(i) \text{ for every } i \in I\}.$$

The alternative notation `F_i = F(i)` is also introduced.

For sets `A` and `B`, the *function space* `ᴬB` is

$$^{A}B = \{F \mid F \text{ is a function from } A \text{ into } B\}.$$

A subset axiom on `𝒫(A × B)` justifies it as a set.

## 7. Lean mapping

Spec layer:

- `def IsFunction`, `def MapsInto`, `def MapsOnto`, `def IsSingleRooted`,
  `def IsOneToOne`, `def IsValueAt` (helper predicate for §5+).
- `FunctionValue` / `FunctionValueAuto` / `FunctionValueWithProof` with
  `F⟮x⟯` and `F⟮x⟯'(...)` notation; see `DESIGN_CHOICE.md` for the rationale.
- `Identity`, `Inverse`, `Composition`, `Restriction`, `Image` with their
  `.Spec` / `.Pair.Spec` lemmas.

Numbered theorems:

- 3E: `thm_3E_domain_inverse`, `thm_3E_range_inverse`,
  `thm_3E_relation_inverse_inverse`.
- 3F: `thm_3F_inverse_single_rooted`,
  `thm_3F_relation_function_single_rooted`.
- 3G: `thm_3G_one_to_one_inverse`, `thm_3G_one_to_one_inverse_ran`,
  plus helpers `inv_is_function`, `preimage_dom`, `preimage_mem_dom`,
  `image_mem_dom_inverse`.
- 3H: `thm_3H_composition_is_function`,
  `def CompositionDomain` + `CompositionDomain.Spec`,
  `thm_3H_composition_domain`, `thm_3H_composition_value_equal`
  (with helpers `comp_dom_mem_inner_dom`, `comp_value_mem_outer_dom`).
- 3I: `thm_3I_inverse_composition`.

3J lives at the bottom of `Set/Ch3/S4_Functions.lean`. The
`Set.Choice` sub-namespace there contains **only** declarations whose
proofs actually invoke an AC axiom — so 3J(b) is in `Choice`, but 3J(a)
and all of its AC-free helpers stay in the plain `Set` namespace. The
file's bottom enforces this split with two `#print axioms` checks.

- AC declarations: `Set.Choice.ChoiceFirstForm` and
  `Set.Choice.choice_first_form` (canonical home: `Set/Choice.lean`,
  which is also where the remaining four equivalent forms of AC will
  live, alongside the second-form `Set.Choice.ChoiceSecondForm`). To
  avoid a circular import, the AC predicates state "function" inline as
  `IsRelation H ∧ ∀ x ∈ dom H, ∃! y, ⟪x, y⟫ ∈ H` — definitionally equal
  to `IsFunction H`, so consumers in `S4_Functions.lean` and downstream
  destructure it directly as an `IsFunction`.
- Visibility marker: `S4_Functions.lean` `#check`s
  `@Choice.ChoiceFirstForm` and `@Choice.choice_first_form` at the top
  (right where Enderton introduces them on p.49), and the bottom of the
  file reopens `namespace Choice` so the axiom is in scope **only**
  inside the 3J(b) proof.
- AC-free helpers (plain `Set` namespace):
  - `LeftInverseRelation F B a₀ := F⁻¹ ∪ (B - ran F) ⨯ {a₀}` plus
    `LeftInverseRelation.Spec`. This is the set named `G` in
    Enderton's Fig. 10(a); when `F` is one-to-one it is *already* a
    function, so no AC is needed.
  - `one_to_one_preimage_unique` — single-rootedness on the entire
    range.
- AC-free theorem (plain `Set` namespace):
  - `thm_3J_a_left_inverse_iff_one_to_one`. The (⇒) direction proves
    `LeftInverseRelation F B a₀` is a function by case-analysis on
    membership (`ran F` vs. `B - ran F`), using
    `one_to_one_preimage_unique` for the `ran F` half.
- AC-dependent theorem (inside `Set.Choice`):
  - `Set.Choice.thm_3J_b_right_inverse_iff_onto`. The (⇒) direction is the
    textbook's first appeal to AC: take `R = F⁻¹` and apply
    `choice_first_form` to extract the right inverse `H`.

3K and 3L (full coverage; the previously missing arbitrary-family and
single-rooted equality items are now in place):

- Family construction: `ImageFamily F 𝒜 := {F⟦A⟧ | A ∈ 𝒜}` with
  `ImageFamily.Spec` and `ImageFamily.Nonempty`.
- 3K(a): `thm_3Ka_image_union` (binary), `thm_3Ka_image_bigUnion` (arbitrary).
- 3K(b): `thm_3Kb_image_inter_subset` (binary, subset),
  `thm_3Kb_image_bigInter_subset` (arbitrary, subset),
  `thm_3Kb_image_inter_eq_of_single_rooted` (binary, equality),
  `thm_3Kb_image_bigInter_eq_of_single_rooted` (arbitrary, equality).
- 3K(c): `thm_3Kc_image_diff_subset` (subset),
  `thm_3Kc_image_diff_eq_of_single_rooted` (equality).
- 3L: `cor_3La_inverse_image_bigUnion`,
  `cor_3Lb_inverse_image_bigInter`,
  `cor_3Lc_inverse_image_diff`.
- Binary convenience corollaries (not part of 3L proper):
  `inverse_image_union`, `inverse_image_inter`, `inverse_image_diff`.

Auxiliary items used in later sections:

- `IndexedUnion` (no preconditions) and `IndexedIntersection`
  (`hI : I.Nonempty` plus `hDom : I ⊆ dom F`, matching Enderton's
  "provided that I is nonempty" once F is a function with `dom F ⊇ I`),
  together with the helper `restriction_range_nonempty`.
- `FunctionSpace` and `FunctionSpace.Spec` (the set `ᴬB`).

Items not part of Enderton's Ch 3.4 (moved out of this file):

- `GraphOn` and its lemmas (`GraphOn.Spec`, `GraphOn.Pair.Spec`,
  `GraphOn.mapsInto`) packaged a Lean meta-function `f : Set → Set` as a
  set-theoretic graph `{⟪x, f x⟫ | x ∈ A}`. They are pure scaffolding for
  Chapter 4 (the Peano-isomorphism proof in `Set/Ch4/S3_RecursionOnOmega.lean`
  and the arithmetic recurrences in `Set/Ch4/S4_Arithmetic.lean`), so they
  now live at the top of `Set/Ch4/S3_RecursionOnOmega.lean` rather than
  cluttering the Enderton-aligned Ch 3.4 file.

## 8. Cross-file linkage

- The first-form Axiom of Choice (`Set.Choice.choice_first_form`) is
  declared in `Set/Choice.lean` (the single home for all six equivalent
  AC forms, by project convention) and `#check`'d at the introduction
  point inside `Set/Ch3/S4_Functions.lean`. The reopened
  `namespace Choice` at the bottom of `S4_Functions.lean` is the only
  scope in that file where the axiom is accessible.
- The infinite Cartesian product `Π_{i ∈ I} H(i)` and the second-form AC
  application live in `Set/Ch3/S5_InfiniteCartesianProducts.lean`
  (Enderton §3.5).
- Exercise 26 (the second halves of 3K(a) and 3K(b)) is now discharged by
  the arbitrary-form theorems above; we use those rather than leaving the
  arbitrary forms as user-facing exercises.

## Workflow note

When editing this section, keep `TODO.md` (Functions block) and the Lean
file aligned with the numbered list above. The transcription doubles as a
checklist: any 3K/3L item present here that lacks a corresponding Lean
theorem indicates the work is incomplete.
