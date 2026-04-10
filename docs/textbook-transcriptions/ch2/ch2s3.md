# Chapter 2 Section 3 (Textbook Transcription)

Temporary transcription from the provided Enderton images.

## Fixed-space abbreviation and De Morgan

Often one considers sets that are all subsets of a fixed "space" `S`.
If `A ⊆ S` and `B ⊆ S`, abbreviate `S - A` by `-A` (with `S` understood).
In this abbreviation:

- `-(A ∪ B) = -A ∩ -B`
- `-(A ∩ B) = -A ∪ -B`

Lean mapping in this project (with fixed `S`):

- `theorem Union.deMorgan_space (A B S : Set) : S - (A ∪ B) = (S - A) ∩ (S - B)`
- `theorem Intersection.deMorgan_space (A B S : Set) : S - (A ∩ B) = (S - A) ∪ (S - B)`

Further (still under `A ⊆ S`):

- `A ∪ S = S`
- `A ∩ S = A`
- `A ∪ -A = S`
- `A ∩ -A = ∅`

## Monotonicity and antimonotonicity

For inclusion:

- `A ⊆ B => A ∪ C ⊆ B ∪ C`
- `A ⊆ B => A ∩ C ⊆ B ∩ C`
- `A ⊆ B => ⋃A ⊆ ⋃B`

Antimonotone results:

- `A ⊆ B => C - B ⊆ C - A`
- `∅ ≠ A ⊆ B => ⋂B ⊆ ⋂A`

## Distributive laws with arbitrary unions/intersections

For `ℬ ≠ ∅`:

- `A ∪ ⋂ℬ = ⋂{A ∪ X | X ∈ ℬ}`

And:

- `A ∩ ⋃ℬ = ⋃{A ∩ X | X ∈ ℬ}`

Notation reminder on the RHS:

- `{A ∪ X | X ∈ ℬ}` means "the set of all `A ∪ X` with `X ∈ ℬ`"
- `{C - X | X ∈ 𝒜}` means "the set of all `C - X` with `X ∈ 𝒜`"
- `{𝒫X | X ∈ 𝒜}` means "the set of all `𝒫X` with `X ∈ 𝒜`"

## De Morgan laws for families (`𝒜 ≠ ∅`)

- `C - ⋃𝒜 = ⋂{C - X | X ∈ 𝒜}`
- `C - ⋂𝒜 = ⋃{C - X | X ∈ 𝒜}`

### Textbook proof sketch (transcribed from image)

To prove, for example, that for nonempty `𝒜` the equation

- `C - ⋃𝒜 = ⋂{C - X | X ∈ 𝒜}`

holds, argue:

- `t ∈ C - ⋃𝒜`
- `=> t ∈ C`, but `t` belongs to no member of `𝒜`
- `=> t ∈ C - X` for every `X ∈ 𝒜`
- `=> t ∈ ⋂{C - X | X ∈ 𝒜}`

Furthermore, every step reverses, so `=>` can be replaced by `<=>`.

Textbook remark: where do we use the fact that `𝒜 ≠ ∅`?

If `⋃𝒜 ⊆ S`, these can be written as:

- `-⋃𝒜 = ⋂{-X | X ∈ 𝒜}`
- `-⋂𝒜 = ⋃{-X | X ∈ 𝒜}`

## Final remark on notation

Alternative equivalent notations:

- `⋂_{X ∈ ℬ} (A ∪ X)` for `⋂{A ∪ X | X ∈ ℬ}`
- `⋃_{X ∈ 𝒜} (C - X)` for `⋃{C - X | X ∈ 𝒜}`
