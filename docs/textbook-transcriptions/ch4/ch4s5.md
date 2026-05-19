# Ch4 Section 5 (Ordering on \(\omega\)) - Textbook Extraction Draft

Source: Enderton, Chapter 4 "Ordering on \(\omega\)", pp. 83-88 in `Enderton_Textbook.pdf`.

This section remains fully set-theoretic: order is defined by membership between
von Neumann naturals, and all proofs avoid Lean primitive `Nat`.

## Narrative (book)

- Define order on \(\omega\):
  - \(m < n \iff m \in n\)
  - \(m \le n \iff (m \in n \lor m = n)\)
- Prove comparison structure (4L + trichotomy): successor compatibility and
  irreflexivity, then case-split comparison between two naturals.
- Derive subset characterizations (4M):
  - \(m \in n \iff m \subset n\)
  - \(m \le n \iff m \subseteq n\)
- Prove monotonicity/cancellation consequences (4N, 4P) using arithmetic from S4.
- Prove well-ordering of \(\omega\), then derive:
  - no descending \(\omega\)-sequence (4Q),
  - strong induction principle.

## Lean mapping (`Set/Ch4/S5_OrderingOnOmega.lean`)

Public (textbook-facing):

- `def NatLt (m n : Set) : Prop := m ∈ n`
- `def NatLe (m n : Set) : Prop := m ∈ n ∨ m = n`
- `theorem natural_succ_mem_iff ...`
- `theorem natural_not_mem_self_4L ...`
- `theorem natural_trichotomy ...`
- `theorem natural_mem_iff_proper_subset ...`
- `theorem natural_le_iff_subset ...`
- `theorem thm_4N_order_preservation ...`
- `theorem cor_4P_cancellation ...`
- `theorem omega_well_ordering ...`
- `theorem no_descending_omega_sequence ...`
- `theorem strong_induction_omega ...`

Public helpers retained for downstream reuse:

- `natural_mem_implies_subset`, `natural_mem_implies_ne`,
- `natural_zero_eq_or_mem`, `natural_compare`,
- `nat_order_preserved_by_add`, `nat_order_preserved_by_mul_succ_factor`,
- `nat_order_preserved_by_mul_nonzero`,
- `nat_add_right_cancel`, `nat_mul_right_cancel`.

Cross-section note:

- `natural_not_mem_self_4L` is the S5 textbook-facing 4L(b) theorem and is proved
  by reusing the foundational theorem `natural_not_mem_self` from
  `Set/Ch4/S2_PeanosPostulates.lean`.

## Proof-flow sketch in this repo

1. Build comparison core from transitivity of naturals and successor lemmas.
2. Package trichotomy and subset characterizations.
3. Reuse S4 arithmetic recursion theorems to prove order preservation and cancellation.
4. Use trichotomy to prove well-ordering, then derive 4Q and strong induction.

## Workflow note

After changing `Set/Ch4/S5_OrderingOnOmega.lean`, keep this draft and the
Ordering section in `TODO.md` synchronized.
