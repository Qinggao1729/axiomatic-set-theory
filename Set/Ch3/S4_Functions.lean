import Set.Ch3.S2_Relations
import Set.Ch2.S2_ArbitraryUnionsIntersections
import Set.SimpAttrs

/-!
# Chapter 3, Section 4: Functions

Function definitions and theorems (3E/3F/3G/3H/3I/3K/3L-style results).

The first-form AC statement is introduced here where Enderton first uses it
(p.49), in plain `Set` as an AC-free proposition. We then enter `Choice`
only for the axiom declaration, exit immediately, and later reopen `Choice`
only for the AC-dependent theorem 3J(b). Everything else in §Functions
remains AC-free.
-/

namespace Set

/-- [Enderton Ch3 §4, p.42] A function is a relation `F` such that for each `x ∈ dom F`
there is only one `y` such that `xFy`. -/
def IsFunction (F : Set) : Prop :=
  IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟪x, y⟫ ∈ F

lemma function_value_unique (F x y z : Set) (hF : IsFunction F) :
    ⟪x, y⟫ ∈ F → ⟪x, z⟫ ∈ F → y = z := by
  intro hxy hxz
  rcases hF with ⟨_, huniq⟩
  have hxdom : x ∈ dom F := Relation.Pair.mem_dom F x y hxy
  rcases huniq x hxdom with ⟨w, hw, hwuniq⟩
  have hyw : y = w := hwuniq y hxy
  have hzw : z = w := hwuniq z hxz
  exact hyw.trans hzw.symm

/-- [Enderton Ch3 §4, p.43] "`F` maps `A` into `B`" iff
`F` is a function, `dom F = A`, and `ran F ⊆ B`. -/
def MapsInto (F A B : Set) : Prop :=
  IsFunction F ∧ (dom F) = A ∧ (ran F) ⊆ B

lemma MapsInto.dom_mem_iff (F A B x : Set) :
  MapsInto F A B → (x ∈ (dom F) ↔ x ∈ A) := by
  intro hMap
  rcases hMap with ⟨_, hDomEq, _⟩
  simp [hDomEq]

/-
Why `aesop safe forward` (not `safe apply`) for side-condition lemmas:

Side-condition lemmas here are "fact extractors" (`MapsInto F A B → IsFunction F`,
`MapsInto F A B → x ∈ A → x ∈ dom F`, ...) used by `function_eval_auto` to
discharge the obligations of `F⟮x⟯` (`IsFunction F` and `x ∈ dom F`).
Forward chaining works better than backward `apply` for them because:

1. *Metavariables.* Backward use of `mapsInto_dom_mem` on goal `x ∈ dom F`
   leaves `?A ?B` as unconstrained holes (`B` doesn't occur in the
   conclusion), so Aesop must guess; forward matching against a concrete
   hypothesis `hMap : MapsInto F A B` instantiates everything.
2. *Goal-shape brittleness.* Backward rules only fire when the goal is
   literally `_ ∈ dom _`; if simp has unfolded it to `∃ y, ⟪x, y⟫ ∈ F`, the
   rule no longer matches. Forward-derived facts persist in the context.
3. *Branching/reuse.* Few rules have a `MapsInto`/`IsCompatible` premise
   (cheap trigger), and a fact derived once is reused by every later
   side-goal (`F⟮x⟯`, `F⟮y⟯`, ...) instead of being re-proved per branch.
-/
lemma isFunction_of_mapsInto {F A B : Set} : MapsInto F A B → IsFunction F :=
  fun h => h.1
attribute [function_eval_sideconds] isFunction_of_mapsInto
attribute [aesop safe forward] isFunction_of_mapsInto

lemma mapsInto_dom_mem {F A B x : Set} :
    MapsInto F A B → x ∈ A → x ∈ dom F := by
  intro hMap hxA
  simpa [hMap.2.1] using hxA
attribute [function_eval_sideconds] mapsInto_dom_mem
attribute [aesop safe forward] mapsInto_dom_mem

/-- [Enderton Ch3 §4, p.43] "`F` maps `A` onto `B`" iff
`F` maps `A` into `B` and `ran F = B`. -/
def MapsOnto (F A B : Set) : Prop :=
  MapsInto F A B ∧ (ran F) = B

/-- [Enderton Ch3 §4, p.43] A relation `R` is single-rooted iff
for each `y ∈ ran R` there is exactly one `x` such that `xRy`. -/
def IsSingleRooted (R : Set) : Prop :=
  ∀ (y : Set), y ∈ (ran R) → ∃! (x: Set), ⟪x, y⟫ ∈ R

/-- [Enderton Ch3 §4, p.43] "`F` is one-to-one" iff
`F` is a function and `F` is single-rooted. -/
def IsOneToOne (F : Set) : Prop := IsFunction F ∧ IsSingleRooted F

lemma isFunction_of_isOneToOne {F : Set} : IsOneToOne F → IsFunction F :=
  fun h => h.1
attribute [function_eval_sideconds] isFunction_of_isOneToOne
attribute [aesop safe forward] isFunction_of_isOneToOne

-- Single-rooted counterpart of `function_value_unique`: a single-rooted R has
-- at most one preimage for each y in its range. Used in 3K equality cases
-- (and 3L) where F is assumed single-rooted instead of a function.
lemma single_rooted_unique (R x x' y : Set) (hSR : IsSingleRooted R) :
    ⟪x, y⟫ ∈ R → ⟪x', y⟫ ∈ R → x = x' := by
  intro hxy hx'y
  have hyRan : y ∈ ran R := (Range.Spec).2 ⟨x, hxy⟩
  rcases hSR y hyRan with ⟨w, _, huniq⟩
  have hxw : x = w := huniq x hxy
  have hx'w : x' = w := huniq x' hx'y
  exact hxw.trans hx'w.symm


/-
Design choice: in Ch3/S4, expose textbook-style "value of a function at x".
This notation is now used in 3G-style statements/proofs in this file.
We also define `IsValueAt` here, and plan to prefer that lighter predicate style
in Ch3/S5 and later sections when statement-level obligations become heavy.
-/

-- Value-at predicate: F is a function and ⟪x, y⟫ ∈ F.
-- Intended as the lighter statement style for Ch3/S5 and onward.
def IsValueAt (F x y : Set) : Prop :=
  IsFunction F ∧ ⟪x, y⟫ ∈ F

/-- Auto-solver for function-evaluation side conditions. -/
syntax "function_eval_auto" : tactic

/-- Debug variant: tries to emit `simp?` suggestions, then solves like `function_eval_auto`.
If it succeeds but does not emit suggestions, it is solve by `assumption`. -/
syntax "function_eval_auto?" : tactic

--TODO: Better tactics
macro_rules
  | `(tactic| function_eval_auto) => `(tactic|
    solve
    | assumption
    -- Directed apply/exact-style search over registered side-condition lemmas.
    | solve_by_elim
    -- First try controlled `only` mode if broad simp does not close the goal.
    | simp only [function_eval_sideconds, prop_simps]
    | simp only [set_spec_simps, function_eval_sideconds, prop_simps]
    | simp_all only [function_eval_sideconds, prop_simps]
    | simp_all only [set_spec_simps, function_eval_sideconds, prop_simps]
    -- Thrn try broader `simp_all` (without `only`) for convenience.
    | simp [function_eval_sideconds]
    -- | simp [set_spec_simps, function_eval_sideconds]
    | simp_all [function_eval_sideconds]
    -- | simp_all [set_spec_simps, function_eval_sideconds]
    | aesop

  )

macro_rules
  | `(tactic| function_eval_auto?) => `(tactic|
    solve
    | assumption
    | solve_by_elim
    -- Branches intentionally mirror `function_eval_auto`, replacing
    -- `simp_all` with `simp_all?`.
    | simp? only [function_eval_sideconds, prop_simps]
    | simp? only [set_spec_simps, function_eval_sideconds, prop_simps]
    | simp_all? only [function_eval_sideconds, prop_simps]
    | simp_all? only [set_spec_simps, function_eval_sideconds, prop_simps]
    | simp? [function_eval_sideconds]
    -- | simp [set_spec_simps, function_eval_sideconds]
    | simp_all? [function_eval_sideconds]
    -- | simp_all? [set_spec_simps, function_eval_sideconds]
    | aesop?
  )


/--[Enderton Ch3 §4, p.43] For a function `F` and `x ∈ dom F`, the unique
`y` with `xFy` is denoted `F(x)`.

Mirrors Lean's list/array indexing (`GetElem.getElem`): a single core
evaluator whose side condition `IsFunction F ∧ x ∈ dom F` plays the role of
`valid xs i`. The `F⟮x⟯` notation discharges it by tactic (like `xs[i]`),
while `F⟮x⟯'(p)` passes the proof directly (like `xs[i]'p`).-/
noncomputable def FunctionValue
    (F x : Set) (h : IsFunction F ∧ x ∈ dom F) : Set :=
  Classical.choose (h.1.2 x h.2)

/--
Textbook-style automatic function evaluation.
Expands at use-site to explicit side-condition goals:
`IsFunction F` and `x ∈ dom F` (solved by `function_eval_auto`).
-/
syntax:max term "⟮" term "⟯" : term

/--
Logging variant of automatic function evaluation.
Expands at use-site to explicit side-condition goals:
`IsFunction F` and `x ∈ dom F` (solved by `function_eval_auto?`).
-/
syntax:max term "⟮" term "⟯?" : term

/-- Manual function evaluation, like `xs[i]'p`: pass the side-condition
proof `IsFunction F ∧ x ∈ dom F` directly. -/
syntax:max term "⟮" term "⟯'(" term ")" : term

macro_rules
  | `($F⟮$x⟯) => `(FunctionValue $F $x ⟨by function_eval_auto, by function_eval_auto⟩)
  -- TODO: Better printing
  -- | `($F⟮$x⟯?) => `(FunctionValue $F $x ⟨by function_eval_auto?, by function_eval_auto?⟩)
  | `($F⟮$x⟯'($p)) => `(FunctionValue $F $x $p)

/-- Pretty-print `FunctionValue` applications back to `F⟮x⟯'(h)` in goals
and hypotheses, instead of kernel-style `f.FunctionValue i ...` display. -/
@[app_unexpander FunctionValue]
def unexpandFunctionValue : Lean.PrettyPrinter.Unexpander
  | `($_ $F $x $h) => `($F⟮$x⟯'($h))
  | _ => throw ()

lemma FunctionValue.Spec
    (F x : Set) (hF : IsFunction F) (hxdom : x ∈ dom F) :
    ⟪x, F⟮x⟯⟫ ∈ F :=
  (Classical.choose_spec (hF.2 x hxdom)).1

lemma FunctionValue.mem_ran
    (F x : Set) (hF : IsFunction F) (hxdom : x ∈ dom F) :
    F⟮x⟯ ∈ ran F := by
  exact Relation.Pair.mem_ran F x F⟮x⟯ (FunctionValue.Spec F x hF hxdom)

lemma FunctionValue.eq_of_pair
    (F x y : Set) (hF : IsFunction F)
    (hxy : ⟪x, y⟫ ∈ F) :
    FunctionValue F x ⟨hF, Relation.Pair.mem_dom F x y hxy⟩ = y := by
  have hxdom : x ∈ dom F := Relation.Pair.mem_dom F x y hxy
  have huniq : ∀ z, ⟪x, z⟫ ∈ F → z = FunctionValue F x ⟨hF, hxdom⟩ :=
    (Classical.choose_spec (hF.2 x hxdom)).2
  exact (huniq y hxy).symm

lemma FunctionValue.eq_of_pair'
    (F x y : Set) (h : IsFunction F ∧ x ∈ dom F)
    (hxy : ⟪x, y⟫ ∈ F) :
    F⟮x⟯'(h) = y :=
  FunctionValue.eq_of_pair F x y h.1 hxy

/-- [Enderton Ch3 §4, p.47] "`I_dom G`, the identity function on dom `G`."
Enderton uses the identity function `I_A` on a set `A` (e.g. in Theorems 3H, 3J and
Exercise 23) without a standalone Definition block; defined here as
`I_A = {⟨x, x⟩ | x ∈ A}`. -/
noncomputable def Identity (A : Set) : Set :=
  Comprehension (λ w ↦ ∃ x, x ∈ A ∧ w = ⟪x, x⟫) (A ⨯ A)

@[simp]
lemma Identity.Spec_full {A w : Set} : w ∈ Identity A ↔ w ∈ (A ⨯ A) ∧ ∃ x, x ∈ A ∧ w = ⟪x, x⟫ := by
  simp [Identity, Comprehension.Spec]
@[simp]
lemma Identity.Spec {A w : Set} : w ∈ Identity A ↔ ∃ x, x ∈ A ∧ w = ⟪x, x⟫ := by
  constructor
  · intro hw
    exact (Identity.Spec_full).1 hw |>.2
  · intro hw
    rcases hw with ⟨x, hxA, hEq⟩
    have hProd : ⟪x, x⟫ ∈ (A ⨯ A) := by
      rw [cor_3C_product_spec]
      exact ⟨x, x, hxA, hxA, rfl⟩
    exact (Identity.Spec_full).2 ⟨by simpa [hEq] using hProd, ⟨x, hxA, hEq⟩⟩
attribute [set_spec_simps] Identity.Spec

lemma Identity.Pair.Spec {A x y : Set} :
    ⟪x, y⟫ ∈ Identity A ↔ x ∈ A ∧ y = x := by
  constructor
  · intro hxy
    rcases (Identity.Spec).1 hxy with ⟨u, huA, hEq⟩
    rcases (thm_3A_ordered_pair_uniqueness x y u u).1 hEq with ⟨hxu, hyu⟩
    subst hxu
    exact ⟨huA, hyu⟩
  · intro hxy
    rcases hxy with ⟨hxA, hyx⟩
    subst y
    apply (Identity.Spec).2
    exact ⟨x, hxA, rfl⟩
attribute [set_spec_simps] Identity.Pair.Spec

/-
Function operations [Enderton, p. 44]
-/
/-- [Enderton Ch3 §4, p.44] "The *inverse* of `F` is the set `F⁻¹ = {⟨u, v⟩ | vFu}`." -/
noncomputable def Inverse (F : Set) :=
  Comprehension (λ w ↦ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ w = ⟪v, u⟫) ((ran F) ⨯ (dom F))

@[simp]
lemma Inverse.Spec {F x : Set} : x ∈ Inverse F ↔ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ x = ⟪v, u⟫ := by
  rw [Inverse, Comprehension.Spec]
  constructor
  · intro hx
    exact hx.2
  · intro hx
    rcases hx with ⟨u, v, huvF, hxEq⟩
    have hvRan : v ∈ ran F := (Range.Spec).2 ⟨u, huvF⟩
    have huDom : u ∈ dom F := (Domain.Spec).2 ⟨v, huvF⟩
    have hxProd : x ∈ (ran F) ⨯ (dom F) := by
      subst hxEq
      exact (cor_3C_product_spec).2 ⟨v, u, hvRan, huDom, rfl⟩
    exact ⟨hxProd, ⟨u, v, huvF, hxEq⟩⟩
attribute [set_spec_simps] Inverse.Spec

@[simp]
lemma Inverse.Pair.Spec {F x y : Set} : ⟪x, y⟫ ∈ Inverse F ↔ ⟪y, x⟫ ∈ F := by
  rw [Inverse.Spec]
  constructor
  · intro h
    rcases h with ⟨u, v, huv, hEq⟩
    rcases (thm_3A_ordered_pair_uniqueness x y v u).1 hEq with ⟨hxv, hyu⟩
    subst hxv hyu
    exact huv
  · intro h
    exact ⟨y, x, h, rfl⟩
attribute [set_spec_simps] Inverse.Pair.Spec

postfix:90 "⁻¹" => Inverse

/-- [Enderton Ch3 §4, p.44] "The *composition* of `F` and `G` is the set
`F ∘ G = {⟨u, v⟩ | ∃t(uGt & tFv)}`." -/
noncomputable def Composition (F G : Set) :=
  Comprehension
    (λ w ↦ ∃ (u v t : Set), ⟪u, t⟫ ∈ G ∧ ⟪t, v⟫ ∈ F ∧ w = ⟪u, v⟫)
    ((dom G) ⨯ (ran F))

@[simp]
lemma Composition.Spec_full {F G x : Set} : x ∈ Composition F G ↔ (x ∈ ((dom G) ⨯ (ran F))) ∧ ∃ (u v t : Set), ⟪u, t⟫ ∈ G ∧ ⟪t, v⟫ ∈ F ∧ x = ⟪u, v⟫ := by
  simp [Composition, Comprehension.Spec]
@[simp]
lemma Composition.Spec {F G x : Set} : x ∈ Composition F G ↔ ∃ (u v t : Set), ⟪u, t⟫ ∈ G ∧ ⟪t, v⟫ ∈ F ∧ x = ⟪u, v⟫ := by
  constructor
  · intro hx
    exact (Composition.Spec_full).1 hx |>.2
  · intro hx
    rcases hx with ⟨u, v, t, hut, htv, hEq⟩
    have huDom : u ∈ dom G := (Domain.Spec).2 ⟨t, hut⟩
    have hvRan : v ∈ ran F := (Range.Spec).2 ⟨t, htv⟩
    have hProd : ⟪u, v⟫ ∈ ((dom G) ⨯ (ran F)) :=
      (cor_3C_product_spec).2 ⟨u, v, huDom, hvRan, rfl⟩
    exact (Composition.Spec_full).2 ⟨by simpa [hEq] using hProd, ⟨u, v, t, hut, htv, hEq⟩⟩
attribute [set_spec_simps] Composition.Spec

@[simp]
lemma Composition.Pair.Spec {F G x y : Set} :
    ⟪x, y⟫ ∈ Composition F G ↔ ∃ t, ⟪x, t⟫ ∈ G ∧ ⟪t, y⟫ ∈ F := by
  rw [Composition.Spec]
  constructor
  · intro h
    rcases h with ⟨u, v, t, hu, hv, hEq⟩
    rcases (thm_3A_ordered_pair_uniqueness x y u v).1 hEq with ⟨hxu, hyv⟩
    subst hxu hyv
    exact ⟨t, hu, hv⟩
  · intro h
    rcases h with ⟨t, hxt, hty⟩
    exact ⟨x, y, t, hxt, hty, rfl⟩
attribute [set_spec_simps] Composition.Pair.Spec

infixr:90 " ∘ " => Composition

/-- [Enderton Ch3 §4, p.44] "The *restriction* of `F` to `A` is the set
`F ↾ A = {⟨u, v⟩ | uFv & u ∈ A}`." -/
noncomputable def Restriction (F : Set) (C : Set) :=
  Comprehension (λ w ↦ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ u ∈ C ∧ w = ⟪u, v⟫) F

@[simp]
lemma Restriction.Spec_full {F C w : Set} : w ∈ Restriction F C ↔ w ∈ F ∧ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ u ∈ C ∧ w = ⟪u, v⟫ := by
  simp [Restriction, Comprehension.Spec]
@[simp]
lemma Restriction.Spec {F C w : Set} : w ∈ Restriction F C ↔ ∃ (u v : Set), ⟪u, v⟫ ∈ F ∧ u ∈ C ∧ w = ⟪u, v⟫ := by
  constructor
  · intro hw
    exact (Restriction.Spec_full).1 hw |>.2
  · intro hw
    rcases hw with ⟨u, v, huvF, huC, hEq⟩
    exact (Restriction.Spec_full).2 ⟨by simpa [hEq] using huvF, ⟨u, v, huvF, huC, hEq⟩⟩
attribute [set_spec_simps] Restriction.Spec

@[simp]
lemma Restriction.Pair.Spec {F C u v : Set} : ⟪u, v⟫ ∈ Restriction F C ↔ ⟪u, v⟫ ∈ F ∧ u ∈ C := by
  rw [Restriction.Spec]
  constructor
  · intro h
    rcases h with ⟨x, y, hxy, hxC, hEq⟩
    rcases (thm_3A_ordered_pair_uniqueness u v x y).1 hEq with ⟨hux, hvy⟩
    subst hux hvy
    exact ⟨hxy, hxC⟩
  · intro h
    rcases h with ⟨hF, hC⟩
    exact ⟨u, v, hF, hC, rfl⟩
attribute [set_spec_simps] Restriction.Pair.Spec

infixr:90 " ↾ " => Restriction

/-- [Enderton Ch3 §4, p.44] "The *image* of `A` under `F` is the set
`F⟦A⟧ = ran(F ↾ A) = {v | (∃u ∈ A)uFv}`." -/
-- Image is not a relation, so no Image.Pair.Spec
noncomputable def Image (F : Set) (C : Set) :=
  ran (Restriction F C)
notation:90 F "⟦" A "⟧" => Image F A

@[simp]
lemma Image.Spec {F C y : Set} : y ∈ F⟦C⟧ ↔ ∃ u, u ∈ C ∧ ⟪u, y⟫ ∈ F := by
  rw [Image, Range.Spec]
  constructor
  · intro h
    rcases h with ⟨u, hu⟩
    rw [Restriction.Pair.Spec] at hu
    exact ⟨u, hu.right, hu.left⟩
  · intro h
    rcases h with ⟨u, huC, huF⟩
    exact ⟨u, (Restriction.Pair.Spec).2 ⟨huF, huC⟩⟩
attribute [set_spec_simps] Image.Spec

/-- [Enderton Ch3 §4, p.46] "Theorem 3E For a set `F`, dom `F⁻¹` = ran `F` and
ran `F⁻¹` = dom `F`. For a relation `F`, `(F⁻¹)⁻¹ = F`." (Part: dom `F⁻¹` = ran `F`.) -/
theorem thm_3E_domain_inverse (F : Set) : (dom (F⁻¹)) = ran F := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro h
    rw [Domain.Spec] at h
    obtain ⟨y, hy⟩ := h
    apply (Range.Spec).2
    exists y
    exact (Inverse.Pair.Spec).1 hy
  · intro h
    rcases (Range.Spec).1 h with ⟨y, hyx⟩
    apply (Domain.Spec).2
    exists y
    exact (Inverse.Pair.Spec).2 hyx

/-- [Enderton Ch3 §4, p.46] "Theorem 3E ... ran `F⁻¹` = dom `F`." -/
theorem thm_3E_range_inverse (F : Set) : (ran (Inverse F)) = dom F := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro h
    rw [Range.Spec] at h
    obtain ⟨y, hy⟩ := h
    have hxy : ⟪x, y⟫ ∈ F := (Inverse.Pair.Spec).1 hy
    apply (Domain.Spec).2
    exact ⟨y, hxy⟩
  · intro h
    rcases (Domain.Spec).1 h with ⟨y, hxy⟩
    apply (Range.Spec).2
    have hxyInv : ⟪y, x⟫ ∈ F⁻¹ := (Inverse.Pair.Spec).2 hxy
    exact ⟨y, hxyInv⟩

/-- [Enderton Ch3 §4, p.46] "Theorem 3E ... For a relation `F`, `(F⁻¹)⁻¹ = F`." -/
theorem thm_3E_relation_inverse_inverse (F : Set) {hF : IsRelation F} : ((F⁻¹)⁻¹) = F := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro hx
    rcases (Inverse.Spec).1 hx with ⟨u, v, huv, rfl⟩
    exact (Inverse.Pair.Spec).1 huv
  · intro hx
    rcases hF x hx with ⟨u, v, rfl⟩
    have hvu : ⟪v, u⟫ ∈ Inverse F := (Inverse.Pair.Spec).2 hx
    exact (Inverse.Pair.Spec).2 hvu

lemma preimage_dom (F : Set) (y : Set) (hy : y ∈ ran F) : y ∈ dom (F⁻¹) := by
  simpa [thm_3E_domain_inverse] using hy
attribute [function_eval_sideconds] preimage_dom


/-- [Enderton Ch3 §4, p.46] "Theorem 3F For a set `F`, `F⁻¹` is a function iff `F`
is single-rooted. A relation `F` is a function iff `F⁻¹` is single-rooted."
(Part: `F⁻¹` is a function iff `F` is single-rooted.) -/
theorem thm_3F_inverse_single_rooted (F : Set) : IsFunction (Inverse F) ↔ IsSingleRooted F := by
  apply Iff.intro
  · intro hFi
    rw [IsFunction, thm_3E_domain_inverse] at hFi
    obtain ⟨_, hFi⟩ := hFi
    rw [IsSingleRooted]
    intro x hx
    obtain ⟨y, hxyInv, huniq⟩ := hFi x hx
    refine ⟨y, (Inverse.Pair.Spec).1 hxyInv, ?_⟩
    intro y' hy'xF
    have hxy'Inv : ⟪x, y'⟫ ∈ Inverse F := (Inverse.Pair.Spec).2 hy'xF
    exact huniq y' hxy'Inv
  · -- IsSingleRooted F → F⁻¹ is a function
    intro h
    rw [IsSingleRooted] at h
    apply And.intro
    · -- Show: F⁻¹ is a relation
      rw [IsRelation]
      intro w hw
      rcases (Inverse.Spec).1 hw with ⟨u, v, _, hEq⟩
      exact ⟨v, u, hEq⟩
    · -- Show: uniqueness of function values
      intro x hx
      rw [thm_3E_domain_inverse] at hx
      obtain ⟨y, hyxF, hyuniq⟩ := h x hx
      refine ⟨y, (Inverse.Pair.Spec).2 hyxF, ?_⟩
      intro y' hy'
      have hy'xF : ⟪y', x⟫ ∈ F := (Inverse.Pair.Spec).1 hy'
      exact hyuniq y' hy'xF


/-- [Enderton Ch3 §4, p.46] "Theorem 3F ... A relation `F` is a function iff `F⁻¹`
is single-rooted." -/
theorem thm_3F_relation_function_single_rooted (F : Set) {hR : IsRelation F} : IsFunction F ↔ IsSingleRooted (Inverse F) := by
  have hInv : IsFunction ((F⁻¹)⁻¹) ↔ IsSingleRooted (F⁻¹) :=
    thm_3F_inverse_single_rooted (F⁻¹)
  simpa [thm_3E_relation_inverse_inverse (F := F) (hF := hR)] using hInv

lemma inv_is_function (F : Set) : IsOneToOne F → IsFunction (F⁻¹) := by
  intro hOne
  exact (thm_3F_inverse_single_rooted F).2 hOne.2
attribute [function_eval_sideconds] inv_is_function

/-- [Enderton Ch3 §4, p.46] "Theorem 3G Assume that `F` is a one-to-one function.
If `x ∈ dom F`, then `F⁻¹(F(x)) = x`. If `y ∈ ran F`, then `F(F⁻¹(y)) = y`."
(Helper: `F(x) ∈ dom F⁻¹` validating the `F⁻¹(F(x))` notation in 3G.) -/
lemma image_mem_dom_inverse
    (F : Set) (hF : IsFunction F) (x : Set) (hx : x ∈ dom F) :
    F⟮x⟯ ∈ dom (F⁻¹) := by
  have hxy : ⟪x, F⟮x⟯⟫ ∈ F := by
    simpa using FunctionValue.Spec F x hF hx
  exact (Domain.Spec).2 ⟨x, (Inverse.Pair.Spec).2 hxy⟩
attribute [function_eval_sideconds] image_mem_dom_inverse

lemma preimage_mem_dom
    (F : Set) (hInv : IsFunction (F⁻¹)) (y : Set) (hy : y ∈ ran F) :
    (F⁻¹)⟮y⟯ ∈ dom F := by
  -- Keep these explicit auto steps so users can click and inspect them.
  have hInv : IsFunction (F⁻¹) := by function_eval_auto?
  have hydom : y ∈ dom (F⁻¹) := by function_eval_auto?
  have hyxInv : ⟪y, (F⁻¹)⟮y⟯⟫ ∈ F⁻¹ := by
    simpa using FunctionValue.Spec (F⁻¹) y
      hInv hydom
  have hxy : ⟪(F⁻¹)⟮y⟯, y⟫ ∈ F :=
    (Inverse.Pair.Spec).1 hyxInv
  exact Relation.Pair.mem_dom F _ y hxy
attribute [function_eval_sideconds] preimage_mem_dom

/-- [Enderton Ch3 §4, p.46] "Theorem 3G Assume that `F` is a one-to-one function.
If `x ∈ dom F`, then `F⁻¹(F(x)) = x`." -/
theorem thm_3G_one_to_one_inverse (F : Set) :
    ∀ hOne : IsOneToOne F,
    ∀ x, ∀ hx : x ∈ dom F,
    F⁻¹⟮F⟮x⟯⟯ = x := by
  intro hOne x hx
  -- One can see how the side conditions are automatically discharged by `function_eval_auto?`.
  have hF : IsFunction F := by function_eval_auto?
  have hxdom : x ∈ dom F := by function_eval_auto?
  have hFInv : IsFunction (F⁻¹) := by function_eval_auto?
  have hxdomInv : F⟮x⟯ ∈ dom (F⁻¹) := by function_eval_auto?

  have hxy : ⟪x, F⟮x⟯⟫ ∈ F := by
    simpa using FunctionValue.Spec F x hOne.1 hx
  have hyxInv : ⟪F⟮x⟯, x⟫ ∈ F⁻¹ := (Inverse.Pair.Spec).2 hxy
  exact FunctionValue.eq_of_pair
    (F := F⁻¹)
    (x := F⟮x⟯)
    (y := x)
    (inv_is_function F hOne)
    hyxInv

/-- [Enderton Ch3 §4, p.46] "Theorem 3G ... If `y ∈ ran F`, then `F(F⁻¹(y)) = y`." -/
theorem thm_3G_one_to_one_inverse_ran (F : Set) :
    ∀ hOne : IsOneToOne F,
    ∀ y, ∀ hy : y ∈ ran F,
    F ⟮F⁻¹⟮y⟯⟯ = y := by
  intro hOne y hy
  -- have hinvfunc : F⁻¹.IsFunction := inv_is_function F hOne
  -- have hydominv : y ∈ dom F⁻¹ := preimage_dom F y hy
  have hinvfunc : IsFunction (F⁻¹) := by function_eval_auto?
  have hydominv : y ∈ dom F⁻¹ := by function_eval_auto?
  have hF : IsFunction F := by function_eval_auto?
  have hxdom : F⁻¹⟮y⟯ ∈ dom F := by function_eval_auto?

  have hyxInv : ⟪y, F⁻¹⟮y⟯⟫ ∈ F⁻¹ := by
    simpa using FunctionValue.Spec (F⁻¹) y hinvfunc hydominv
  have hxy : ⟪F⁻¹⟮y⟯, y⟫ ∈ F := (Inverse.Pair.Spec).1 hyxInv
  exact FunctionValue.eq_of_pair
    (F := F)
    (x := F⁻¹⟮y⟯)
    (y := y)
    hOne.1
    hxy

/-- [Enderton Ch3 §4, p.47] "Theorem 3H Assume that `F` and `G` are functions. Then
`F ∘ G` is a function, its domain is `{x ∈ dom G | G(x) ∈ dom F}`, and for `x` in its
domain, `(F ∘ G)(x) = F(G(x))`." (Part: `F ∘ G` is a function.) -/
theorem thm_3H_composition_is_function (F G : Set) : IsFunction F → IsFunction G → IsFunction (Composition F G) := by
  intro hF hG
  apply And.intro
  · intro w hw
    rw [Composition.Spec] at hw
    rcases hw with ⟨u, v, _, _, _, hEq⟩
    exact ⟨u, v, hEq⟩
  · intro x hx
    rw [Domain.Spec] at hx
    rcases hx with ⟨y, hxy⟩
    rcases (Composition.Pair.Spec).1 hxy with ⟨t, hxt, hty⟩
    refine ⟨y, hxy, ?_⟩
    intro y' hxy'
    rcases (Composition.Pair.Spec).1 hxy' with ⟨t', hxt', ht'y'⟩
    have htt' : t = t' := function_value_unique G x t t' hG hxt hxt'
    subst htt'
    exact (function_value_unique F t y y' hF hty ht'y').symm
attribute [function_eval_sideconds] thm_3H_composition_is_function

/-- [Enderton Ch3 §4, p.47] "Theorem 3H ... its domain is `{x ∈ dom G | G(x) ∈ dom F}`."
(Helper carrier set naming the domain of `F ∘ G`.) -/
noncomputable def CompositionDomain (F G : Set) : Set :=
  Comprehension (λ x ↦ ∃ t, ⟪x, t⟫ ∈ G ∧ t ∈ (dom F)) (dom G)

lemma CompositionDomain.Spec_full {F G x : Set} :
    x ∈ CompositionDomain F G ↔ x ∈ (dom G) ∧ ∃ t, ⟪x, t⟫ ∈ G ∧ t ∈ (dom F) := by
  simp [CompositionDomain, Comprehension.Spec]
lemma CompositionDomain.Spec {F G x : Set} :
    x ∈ CompositionDomain F G ↔ ∃ t, ⟪x, t⟫ ∈ G ∧ t ∈ (dom F) := by
  constructor
  · intro hx
    exact (CompositionDomain.Spec_full).1 hx |>.2
  · intro hx
    rcases hx with ⟨t, hxt, htDomF⟩
    have hxDomG : x ∈ dom G := (Domain.Spec).2 ⟨t, hxt⟩
    exact (CompositionDomain.Spec_full).2 ⟨hxDomG, ⟨t, hxt, htDomF⟩⟩

/-- [Enderton Ch3 §4, p.47] "Theorem 3H ... its domain is `{x ∈ dom G | G(x) ∈ dom F}`." -/
theorem thm_3H_composition_domain (F G : Set) :
    (dom (Composition F G)) = CompositionDomain F G := by
  apply extensionality
  intro x
  apply Iff.intro
  · intro hx
    rw [Domain.Spec] at hx
    rcases hx with ⟨y, hxy⟩
    rcases (Composition.Pair.Spec).1 hxy with ⟨t, hxt, hty⟩
    rw [CompositionDomain.Spec]
    exact ⟨t, hxt, Relation.Pair.mem_dom F t y hty⟩
  · intro hx
    rw [CompositionDomain.Spec] at hx
    rcases hx with ⟨t, hxt, htDomF⟩
    rw [Domain.Spec] at htDomF
    rcases htDomF with ⟨y, hty⟩
    rw [Domain.Spec]
    exact ⟨y, (Composition.Pair.Spec).2 ⟨t, hxt, hty⟩⟩
  attribute [function_eval_sideconds] thm_3H_composition_domain

/-- [Enderton Ch3 §4, p.47] "Theorem 3H ... for `x` in its domain, `(F ∘ G)(x) = F(G(x))`."
(Helper: from `x ∈ dom (F ∘ G)` derive `x ∈ dom G`, validating `G(x)`.) -/
lemma comp_dom_mem_inner_dom (F G x : Set) (hx : x ∈ dom (Composition F G)) :
    x ∈ dom G := by
  rw [thm_3H_composition_domain, CompositionDomain.Spec] at hx
  rcases hx with ⟨t, hxt, _⟩
  exact Relation.Pair.mem_dom G x t hxt
attribute [function_eval_sideconds] comp_dom_mem_inner_dom
attribute [aesop safe forward] comp_dom_mem_inner_dom

lemma comp_value_mem_outer_dom (F G x : Set) (hG : IsFunction G)
    (hx : x ∈ dom (Composition F G)) :
    G⟮x⟯'(⟨hG, comp_dom_mem_inner_dom F G x hx⟩) ∈ dom F := by
  have hxCD : x ∈ CompositionDomain F G := by
    rw [← thm_3H_composition_domain]; exact hx
  have hxdom : x ∈ dom G := by
    exact comp_dom_mem_inner_dom F G x hx
  rcases (CompositionDomain.Spec).1 hxCD with ⟨t, hxt, htDomF⟩
  have hGxG : ⟪x, G⟮x⟯⟫ ∈ G := by
    simpa using
      FunctionValue.Spec G x hG (comp_dom_mem_inner_dom F G x hx)
  have hGx_eq_t : G⟮x⟯ = t :=
    function_value_unique G x _ t hG hGxG hxt
  rw [hGx_eq_t]
  exact htDomF
attribute [function_eval_sideconds] comp_value_mem_outer_dom
attribute [aesop safe forward] comp_value_mem_outer_dom

/-- [Enderton Ch3 §4, p.47] "Theorem 3H ... for `x` in its domain, `(F ∘ G)(x) = F(G(x))`." -/
theorem thm_3H_composition_value_equal
    (F G x : Set) (hF : IsFunction F) (hG : IsFunction G)
    (hx : x ∈ dom (F ∘ G)) :
    (F ∘ G)⟮x⟯
    = F⟮G⟮x⟯'(⟨hG, comp_dom_mem_inner_dom F G x hx⟩)⟯'(
        ⟨hF, comp_value_mem_outer_dom F G x hG hx⟩) := by
  have hFG: IsFunction (F ∘ G):= by function_eval_auto?
  have hxDomG : x ∈ dom G := comp_dom_mem_inner_dom F G x hx
  have hGxDomF : G⟮x⟯ ∈ dom F := comp_value_mem_outer_dom F G x hG hx
  have hxG : ⟪x, G⟮x⟯⟫ ∈ G := by
    simpa using FunctionValue.Spec G x hG hxDomG
  have hGxF : ⟪G⟮x⟯, F⟮G⟮x⟯⟯⟫ ∈ F := by
    simpa using FunctionValue.Spec F G⟮x⟯ hF hGxDomF
  have hxFG : ⟪x, F⟮G⟮x⟯⟯⟫ ∈ F ∘ G :=
    (Composition.Pair.Spec).2 ⟨_, hxG, hGxF⟩
  exact FunctionValue.eq_of_pair' (Composition F G) x _
    ⟨thm_3H_composition_is_function F G hF hG, hx⟩ hxFG

/-- [Enderton Ch3 §4, p.47] "Theorem 3I For any sets `F` and `G`, `(F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹`." -/
theorem thm_3I_inverse_composition (F G : Set) : (Composition F G)⁻¹ = Composition (Inverse G) (Inverse F) := by
  apply extensionality
  intro w
  apply Iff.intro
  · intro hw
    rw [Inverse.Spec] at hw
    rcases hw with ⟨u, v, huv, rfl⟩
    rcases (Composition.Pair.Spec).1 huv with ⟨t, hut, htv⟩
    exact (Composition.Pair.Spec).2
      ⟨t, (Inverse.Pair.Spec).2 htv, (Inverse.Pair.Spec).2 hut⟩
  · intro hw
    rw [Composition.Spec] at hw
    rcases hw with ⟨u, v, t, hut, htv, rfl⟩
    rw [Inverse.Pair.Spec] at hut htv
    exact (Inverse.Pair.Spec).2
      ((Composition.Pair.Spec).2 ⟨t, htv, hut⟩)

/-
Theorem 3J [Enderton, pp. 48–49].

Part (a) is AC-free; part (b) is the textbook's first appeal to the
Axiom of Choice. We therefore prove (a) (and its supporting construction
`LeftInverseRelation` + `one_to_one_preimage_unique`) in the plain
`Set` namespace, and put **only** 3J(b) inside a reopened `namespace
Choice` block where `choice_first_form` is in scope. The rule of thumb
driving this split: a declaration lives in `Choice` iff its proof
actually uses an AC axiom.

`aesop` is permitted in this section (per project rule) for routine
membership/case bookkeeping; we still keep the high-level structure
explicit.
-/

/-- Two preimages of the same element in a one-to-one function coincide.
AC-free helper used by both 3J(a) and 3J(b). -/
lemma one_to_one_preimage_unique (F x z y : Set) (hInj : IsOneToOne F)
    (hxy : ⟪x, y⟫ ∈ F) (hzy : ⟪z, y⟫ ∈ F) : x = z := by
  rcases hInj with ⟨_, hSR⟩
  have hyRan : y ∈ ran F := Relation.Pair.mem_ran F x y hxy
  rcases hSR y hyRan with ⟨w, _, huniq⟩
  have hxw : x = w := huniq x hxy
  have hzw : z = w := huniq z hzy
  exact hxw.trans hzw.symm

/--
Enderton's "extend `F⁻¹` to all of `B`" construction (Theorem 3J(a) proof).
On `ran F` it agrees with `F⁻¹`; on `B - ran F` it pairs every element
with the fixed `a₀ ∈ A`. AC is not needed: the extension is fully
determined by `a₀`.
-/
noncomputable def LeftInverseRelation (F B a0 : Set) : Set :=
  (F⁻¹) ∪ ((B - ran F) ⨯ Singleton a0)

lemma LeftInverseRelation.Spec {F B a0 u v : Set} :
    ⟪u, v⟫ ∈ LeftInverseRelation F B a0 ↔
      (⟪u, v⟫ ∈ F⁻¹ ∨ (u ∈ (B - ran F) ∧ v = a0)) := by
  constructor
  · intro huv
    rw [LeftInverseRelation, Union.Spec] at huv
    cases huv with
    | inl hInv => exact Or.inl hInv
    | inr hDef =>
      rcases (Product.Spec).1 hDef with ⟨x, y, hxDiff, hySing, hEq⟩
      rcases (OrderedPair.uniqueness u v x y).1 hEq with ⟨hux, hvy⟩
      subst hux
      have hvSing : v ∈ Singleton a0 := by simpa [hvy] using hySing
      exact Or.inr ⟨hxDiff, (Singleton.Spec).1 hvSing⟩
  · intro huv
    rw [LeftInverseRelation, Union.Spec]
    cases huv with
    | inl hInv => exact Or.inl hInv
    | inr hDef =>
      rcases hDef with ⟨huDiff, hvEq⟩
      have hvSing : v ∈ Singleton a0 := by
        rw [Singleton.Spec]; exact hvEq
      exact Or.inr ((Product.Pair.Spec).2 ⟨huDiff, hvSing⟩)

/-- [Enderton Ch3 §4, p.48] "Theorem 3J Assume that `F: A → B`, and that `A` is
nonempty. (a) There exists a function `G: B → A` (a 'left inverse') such that `G ∘ F`
is the identity function `I_A` on `A` iff `F` is one-to-one."
AC-free: the (⇒) direction uses `LeftInverseRelation`, fully determined once a fixed
`a₀ ∈ A` is picked. -/
theorem thm_3Ja_left_inverse_iff_one_to_one
    (F A B : Set) (hMap : MapsInto F A B) (hANon : A.Nonempty) :
    (∃ G, MapsInto G B A ∧ (G ∘ F) = Identity A) ↔ IsOneToOne F := by
  rcases hMap with ⟨hFfun, hDomF, hRanSub⟩
  constructor
  · -- (←) Left-inverse `G` collapses preimages of every `y ∈ ran F`.
    rintro ⟨G, ⟨hGfun, hDomG, _⟩, hComp⟩
    refine ⟨hFfun, ?_⟩
    intro y hyRan
    rcases (Range.Spec).1 hyRan with ⟨x, hxy⟩
    refine ⟨x, hxy, ?_⟩
    intro z hzy
    have hyB : y ∈ B := hRanSub y hyRan
    have hyDomG : y ∈ dom G := by simpa [hDomG] using hyB
    rcases hGfun.2 y hyDomG with ⟨t, hyt, _⟩
    have hxt : ⟪x, t⟫ ∈ Identity A := by
      have : ⟪x, t⟫ ∈ G ∘ F := (Composition.Pair.Spec).2 ⟨y, hxy, hyt⟩
      simpa [hComp] using this
    have hzt : ⟪z, t⟫ ∈ Identity A := by
      have : ⟪z, t⟫ ∈ G ∘ F := (Composition.Pair.Spec).2 ⟨y, hzy, hyt⟩
      simpa [hComp] using this
    have htx : t = x := ((Identity.Pair.Spec).1 hxt).2
    have htz : t = z := ((Identity.Pair.Spec).1 hzt).2
    exact htz.symm.trans htx
  · -- (→) Build `G` directly from `LeftInverseRelation`; no AC needed.
    intro hInj
    rcases hANon with ⟨a0, ha0A⟩
    let G : Set := LeftInverseRelation F B a0
    have hDomG : (dom G) = B := by
      apply extensionality
      intro u
      constructor
      · intro huDom
        rcases (Domain.Spec).1 huDom with ⟨v, huvG⟩
        rcases (LeftInverseRelation.Spec).1 huvG with hInv | hDef
        · have hvuF : ⟪v, u⟫ ∈ F := (Inverse.Pair.Spec).1 hInv
          exact hRanSub u (Relation.Pair.mem_ran F v u hvuF)
        · exact ((Difference.Spec).1 hDef.1).left
      · intro huB
        by_cases huRan : u ∈ ran F
        · rcases (Range.Spec).1 huRan with ⟨x, hxu⟩
          refine (Domain.Spec).2 ⟨x, ?_⟩
          exact (LeftInverseRelation.Spec).2 (Or.inl ((Inverse.Pair.Spec).2 hxu))
        · refine (Domain.Spec).2 ⟨a0, ?_⟩
          exact (LeftInverseRelation.Spec).2
            (Or.inr ⟨(Difference.Spec).2 ⟨huB, huRan⟩, rfl⟩)
    -- `G` is a function because `F` is one-to-one: every `b ∈ ran F`
    -- has a unique preimage, and every `b ∈ B - ran F` is paired with
    -- `a₀` only.
    have hGfun : IsFunction G := by
      refine ⟨?_, ?_⟩
      · intro w hw
        change w ∈ LeftInverseRelation F B a0 at hw
        rw [LeftInverseRelation, Union.Spec] at hw
        cases hw with
        | inl hInv =>
          rcases (Inverse.Spec).1 hInv with ⟨u, v, _, hEq⟩
          exact ⟨v, u, hEq⟩
        | inr hDef =>
          rcases (Product.Spec).1 hDef with ⟨x, y, _, _, hEq⟩
          exact ⟨x, y, hEq⟩
      · intro b hbDom
        rcases (Domain.Spec).1 hbDom with ⟨v, hbvG⟩
        refine ⟨v, hbvG, ?_⟩
        intro v' hbv'G
        rcases (LeftInverseRelation.Spec).1 hbvG with hInv | hDef
        · -- `b ∈ ran F`: `v = F⁻¹(b)`, and by single-rootedness so is `v'`.
          have hvbF : ⟪v, b⟫ ∈ F := (Inverse.Pair.Spec).1 hInv
          have hbRan : b ∈ ran F := Relation.Pair.mem_ran F v b hvbF
          rcases (LeftInverseRelation.Spec).1 hbv'G with hInv' | hDef'
          · have hv'bF : ⟪v', b⟫ ∈ F := (Inverse.Pair.Spec).1 hInv'
            exact (one_to_one_preimage_unique F v v' b hInj hvbF hv'bF).symm
          · exact absurd hbRan ((Difference.Spec).1 hDef'.1).right
        · -- `b ∈ B - ran F`: both `v` and `v'` must equal `a₀`.
          have hbNotRan : b ∉ ran F := ((Difference.Spec).1 hDef.1).right
          rcases (LeftInverseRelation.Spec).1 hbv'G with hInv' | hDef'
          · have hv'bF : ⟪v', b⟫ ∈ F := (Inverse.Pair.Spec).1 hInv'
            exact absurd (Relation.Pair.mem_ran F v' b hv'bF) hbNotRan
          · exact hDef'.2.trans hDef.2.symm
    have hRanGSubA : (ran G) ⊆ A := by
      intro v hvRan
      rcases (Range.Spec).1 hvRan with ⟨u, huvG⟩
      rcases (LeftInverseRelation.Spec).1 huvG with hInv | hDef
      · have hvuF : ⟪v, u⟫ ∈ F := (Inverse.Pair.Spec).1 hInv
        simpa [hDomF] using Relation.Pair.mem_dom F v u hvuF
      · simpa [hDef.2] using ha0A
    refine ⟨G, ⟨hGfun, hDomG, hRanGSubA⟩, ?_⟩
    apply extensionality
    intro w
    constructor
    · intro hwComp
      rcases (Composition.Spec).1 hwComp with ⟨x, z, t, hxtF, htzG, hEqw⟩
      have htRan : t ∈ ran F := Relation.Pair.mem_ran F x t hxtF
      have hztF : ⟪z, t⟫ ∈ F := by
        rcases (LeftInverseRelation.Spec).1 htzG with hInv | hDef
        · exact (Inverse.Pair.Spec).1 hInv
        · exact absurd htRan ((Difference.Spec).1 hDef.1).right
      have hxz : x = z := one_to_one_preimage_unique F x z t hInj hxtF hztF
      have hxA : x ∈ A := by
        simpa [hDomF] using Relation.Pair.mem_dom F x t hxtF
      subst hEqw
      exact (Identity.Pair.Spec).2 ⟨hxA, hxz.symm⟩
    · intro hwId
      rcases (Identity.Spec).1 hwId with ⟨x, hxA, hEqw⟩
      have hxDomF : x ∈ dom F := by simpa [hDomF] using hxA
      rcases hFfun.2 x hxDomF with ⟨y, hxyF, _⟩
      have hyRan : y ∈ ran F := Relation.Pair.mem_ran F x y hxyF
      have hyDomG : y ∈ dom G := by
        simpa [hDomG] using hRanSub y hyRan
      rcases hGfun.2 y hyDomG with ⟨z, hyzG, _⟩
      have hzyF : ⟪z, y⟫ ∈ F := by
        rcases (LeftInverseRelation.Spec).1 hyzG with hInv | hDef
        · exact (Inverse.Pair.Spec).1 hInv
        · exact absurd hyRan ((Difference.Spec).1 hDef.1).right
      have hzx : z = x := one_to_one_preimage_unique F z x y hInj hzyF hxyF
      have hyxG : ⟪y, x⟫ ∈ G := by simpa [hzx] using hyzG
      subst hEqw
      exact (Composition.Pair.Spec).2 ⟨y, hxyF, hyxG⟩

/-- [Enderton Ch3 §4, pp.48-49] "Theorem 3J ... (b) There exists a function `H: B → A`
(a 'right inverse') such that `F ∘ H` is the identity function `I_B` on `B` iff `F` maps
`A` onto `B`." (AC-free direction: right inverse ⇒ onto.) -/
theorem thm_3Jb_right_inverse_implies_onto
    (F A B : Set) (hMap : MapsInto F A B) (_ : A.Nonempty) :
    (∃ H, MapsInto H B A ∧ (F ∘ H) = Identity B) → MapsOnto F A B := by
  rcases hMap with ⟨hFfun, hDomF, hRanSub⟩
  rintro ⟨H, ⟨hHfun, hDomH, hRanHSubA⟩, hComp⟩
  refine ⟨⟨hFfun, hDomF, hRanSub⟩, ?_⟩
  apply extensionality
  intro b
  refine ⟨fun hbRan => hRanSub b hbRan, ?_⟩
  intro hbB
  have hbDomH : b ∈ dom H := by simpa [hDomH] using hbB
  rcases hHfun.2 b hbDomH with ⟨a, hbaH, _⟩
  have haA : a ∈ A := hRanHSubA a (Relation.Pair.mem_ran H b a hbaH)
  have haDomF : a ∈ dom F := by simpa [hDomF] using haA
  rcases hFfun.2 a haDomF with ⟨z, hazF, _⟩
  have hbzId : ⟪b, z⟫ ∈ Identity B := by
    have : ⟪b, z⟫ ∈ F ∘ H := (Composition.Pair.Spec).2 ⟨a, hbaH, hazF⟩
    simpa [hComp] using this
  have hzb : z = b := ((Identity.Pair.Spec).1 hbzId).2
  exact (Range.Spec).2 ⟨a, by simpa [hzb] using hazF⟩

/-
Only declarations whose proofs actually invoke an AC axiom are placed in
`Set.Choice`.
-/
/-- [Enderton Ch3 §4, p.49] "Axiom of Choice (first form) For any relation `R` there
is a function `H ⊆ R` with dom `H` = dom `R`."
Introduced here in the 3J(b) neighborhood, where AC first enters the argument. -/
def ChoiceFirstForm : Prop :=
  ∀ (R : Set), IsRelation R →
    ∃ (H : Set), H ⊆ R ∧ IsFunction H ∧ (dom H) = (dom R)

namespace Choice

/-- [Enderton Ch3 §4, p.49] "Axiom of Choice (first form) For any relation `R` there
is a function `H ⊆ R` with dom `H` = dom `R`." (The axiom itself.) -/
axiom choice_first_form : Set.ChoiceFirstForm

-- Visibility marker at Enderton's introduction point (p.49).
#check @ChoiceFirstForm
#check @Choice.choice_first_form

/-- [Enderton Ch3 §4, pp.48-49] "Theorem 3J ... (b) There exists a function `H: B → A`
(a 'right inverse') such that `F ∘ H` is the identity function `I_B` on `B` iff `F` maps
`A` onto `B`." (AC-dependent direction: onto ⇒ right inverse, via `choice_first_form`.) -/
theorem thm_3Jb_onto_implies_right_inverse_of_choice_first_form
    (F A B : Set) (hMap : MapsInto F A B) (_ : A.Nonempty) :
    MapsOnto F A B → ∃ H, MapsInto H B A ∧ (F ∘ H) = Identity B := by
  rcases hMap with ⟨hFfun, hDomF, hRanSub⟩
  rintro ⟨_, hRanEqB⟩
  let R : Set := F⁻¹
  have hRRel : IsRelation R := by
    intro w hw
    rcases (Inverse.Spec).1 hw with ⟨u, v, _, hEq⟩
    exact ⟨v, u, hEq⟩
  -- AC step: pick a function `H ⊆ R` with full domain `dom R`.
  rcases choice_first_form R hRRel with ⟨H, hHSubR, hHfun, hDomHEqR⟩
  have hDomH : (dom H) = B :=
    hDomHEqR.trans ((thm_3E_domain_inverse F).trans hRanEqB)
  have hRanHSubA : (ran H) ⊆ A := by
    intro a haRan
    rcases (Range.Spec).1 haRan with ⟨b, hbaH⟩
    have habF : ⟪a, b⟫ ∈ F := (Inverse.Pair.Spec).1 (hHSubR _ hbaH)
    simpa [hDomF] using Relation.Pair.mem_dom F a b habF
  refine ⟨H, ⟨hHfun, hDomH, hRanHSubA⟩, ?_⟩
  apply extensionality
  intro w
  constructor
  -- `(F ∘ H) ⊆ I_B`: outputs must agree with the chosen inverse branch.
  · intro hwComp
    rcases (Composition.Spec).1 hwComp with ⟨b, z, a, hbaH, hazF, hEqw⟩
    have habF : ⟪a, b⟫ ∈ F := (Inverse.Pair.Spec).1 (hHSubR _ hbaH)
    have hzb : z = b := function_value_unique F a z b hFfun hazF habF
    have hbB : b ∈ B := by
      simpa [hDomH] using Relation.Pair.mem_dom H b a hbaH
    subst hEqw
    exact (Identity.Pair.Spec).2 ⟨hbB, hzb⟩
  -- `I_B ⊆ (F ∘ H)`: for each `b ∈ B`, use `H`'s chosen preimage.
  · intro hwId
    rcases (Identity.Spec).1 hwId with ⟨b, hbB, hEqw⟩
    have hbDomH : b ∈ dom H := by simpa [hDomH] using hbB
    rcases hHfun.2 b hbDomH with ⟨a, hbaH, _⟩
    have habF : ⟪a, b⟫ ∈ F := (Inverse.Pair.Spec).1 (hHSubR _ hbaH)
    subst hEqw
    exact (Composition.Pair.Spec).2 ⟨a, hbaH, habF⟩

/-- [Enderton Ch3 §4, pp.48-49] "Theorem 3J ... (b) There exists a function `H: B → A`
(a 'right inverse') such that `F ∘ H` is the identity function `I_B` on `B` iff `F` maps
`A` onto `B`." (Full iff, combining the AC-free and AC-dependent directions.) -/
theorem thm_3Jb_right_inverse_iff_onto
    (F A B : Set) (hMap : MapsInto F A B) (hANon : A.Nonempty) :
    (∃ H, MapsInto H B A ∧ (F ∘ H) = Identity B) ↔ MapsOnto F A B := by
  constructor
  -- AC-free direction.
  · exact Set.thm_3Jb_right_inverse_implies_onto F A B hMap hANon
  -- AC-dependent direction via `choice_first_form`.
  · intro hOnto
    exact thm_3Jb_onto_implies_right_inverse_of_choice_first_form
      F A B hMap hANon hOnto

end Choice
-- #check thm_3Jb_right_inverse_iff_onto -- unidentifiable

-- Invariant (kept as a build-time check):
--   `Set.thm_3Ja_left_inverse_iff_one_to_one` must NOT depend on
--   first-form AC, and the AC-dependent 3J(b) theorem must.
-- Both depend on Lean's `Classical.choice` (metatheoretic), but that is
-- separate from the set-theoretic Choice axiom we are tracking here.
#print axioms thm_3Ja_left_inverse_iff_one_to_one
#print axioms Choice.thm_3Jb_right_inverse_iff_onto


/-- [Enderton Ch3 §4, p.50] "Theorem 3K ... `⋃{F⟦A⟧ | A ∈ 𝒜}`."
Auxiliary construction: the family `{F⟦A⟧ | A ∈ 𝒜}` used in the second halves of
3K(a)(b) and throughout 3L. Each member is a subset of `ran F`, so the carrier
`𝒫 (ran F)` is sufficient. -/
noncomputable def ImageFamily (F 𝒜 : Set) : Set :=
  Comprehension (fun w => ∃ A, A ∈ 𝒜 ∧ w = F⟦A⟧) (𝒫 (ran F))

lemma ImageFamily.Spec {F 𝒜 w : Set} :
    w ∈ ImageFamily F 𝒜 ↔ ∃ A, A ∈ 𝒜 ∧ w = F⟦A⟧ := by
  simp only [ImageFamily, Comprehension.Spec, Power.Spec]
  constructor
  · rintro ⟨_, A, hA, hw⟩
    exact ⟨A, hA, hw⟩
  · rintro ⟨A, hA, hw⟩
    refine ⟨?_, A, hA, hw⟩
    subst hw
    intro y hyImg
    rcases (Image.Spec).1 hyImg with ⟨u, _, huy⟩
    exact (Range.Spec).2 ⟨u, huy⟩
attribute [set_spec_simps] ImageFamily.Spec

lemma ImageFamily.Nonempty {F 𝒜 : Set} (h𝒜 : 𝒜.Nonempty) :
    (ImageFamily F 𝒜).Nonempty := by
  rcases h𝒜 with ⟨A, hA⟩
  exact ⟨F⟦A⟧, (ImageFamily.Spec).2 ⟨A, hA, rfl⟩⟩

/-- [Enderton Ch3 §4, p.50] "Theorem 3K ... (a) The image of a union is the union of
the images: `F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧` and `F⟦⋃𝒜⟧ = ⋃{F⟦A⟧ | A ∈ 𝒜}`."
(`F` need not be a function. Binary form.) -/
theorem thm_3Ka_image_union (F A B : Set) : F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧ := by
  apply extensionality
  intro y
  constructor
  · intro h
    rcases (Image.Spec).1 h with ⟨x, hxAB, hxy⟩
    rcases (Union.Spec).1 hxAB with hxA | hxB
    · exact (Union.Spec).2 (Or.inl ((Image.Spec).2 ⟨x, hxA, hxy⟩))
    · exact (Union.Spec).2 (Or.inr ((Image.Spec).2 ⟨x, hxB, hxy⟩))
  · intro h
    rcases (Union.Spec).1 h with hA | hB
    · rcases (Image.Spec).1 hA with ⟨x, hxA, hxy⟩
      exact (Image.Spec).2 ⟨x, (Union.Spec).2 (Or.inl hxA), hxy⟩
    · rcases (Image.Spec).1 hB with ⟨x, hxB, hxy⟩
      exact (Image.Spec).2 ⟨x, (Union.Spec).2 (Or.inr hxB), hxy⟩

/-- [Enderton Ch3 §4, p.50] "Theorem 3K(a) ... `F⟦⋃𝒜⟧ = ⋃{F⟦A⟧ | A ∈ 𝒜}`."
(Arbitrary-family form.) -/
theorem thm_3Ka_image_bigUnion (F 𝒜 : Set) :
    F⟦⋃ 𝒜⟧ = ⋃ (ImageFamily F 𝒜) := by
  apply extensionality
  intro y
  constructor
  · intro hy
    rcases (Image.Spec).1 hy with ⟨x, hxBU, hxy⟩
    rcases (BigUnion.Spec).1 hxBU with ⟨A, hA𝒜, hxA⟩
    refine (BigUnion.Spec).2 ⟨F⟦A⟧, ?_, ?_⟩
    · exact (ImageFamily.Spec).2 ⟨A, hA𝒜, rfl⟩
    · exact (Image.Spec).2 ⟨x, hxA, hxy⟩
  · intro hy
    rcases (BigUnion.Spec).1 hy with ⟨B, hBfam, hyB⟩
    rcases (ImageFamily.Spec).1 hBfam with ⟨A, hA𝒜, hBeq⟩
    subst hBeq
    rcases (Image.Spec).1 hyB with ⟨x, hxA, hxy⟩
    refine (Image.Spec).2 ⟨x, ?_, hxy⟩
    exact (BigUnion.Spec).2 ⟨A, hA𝒜, hxA⟩

/-- [Enderton Ch3 §4, p.50] "Theorem 3K ... (b) The image of an intersection is
included in the intersection of the images: `F⟦A ∩ B⟧ ⊆ F⟦A⟧ ∩ F⟦B⟧` and
`F⟦⋂𝒜⟧ ⊆ ⋂{F⟦A⟧ | A ∈ 𝒜}` for nonempty `𝒜`. Equality holds if `F` is single-rooted."
(Binary subset form.) -/
theorem thm_3Kb_image_inter_subset (F A B : Set) : F⟦A ∩ B⟧ ⊆ F⟦A⟧ ∩ F⟦B⟧ := by
  intro y hy
  rw [Image.Spec] at hy
  rcases hy with ⟨x, hxAB, hxy⟩
  rw [Intersection.Spec] at hxAB
  rw [Intersection.Spec, Image.Spec, Image.Spec]
  exact ⟨⟨x, hxAB.left, hxy⟩, ⟨x, hxAB.right, hxy⟩⟩

/-- [Enderton Ch3 §4, p.50] "Theorem 3K(b) ... `F⟦⋂𝒜⟧ ⊆ ⋂{F⟦A⟧ | A ∈ 𝒜}` for
nonempty `𝒜`." (Arbitrary-family subset form.) -/
theorem thm_3Kb_image_bigInter_subset
    (F 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) :
    F⟦BigIntersection 𝒜 h𝒜⟧
    ⊆ BigIntersection (ImageFamily F 𝒜) (ImageFamily.Nonempty h𝒜) := by
  intro y hy
  rcases (Image.Spec).1 hy with ⟨x, hxBI, hxy⟩
  refine (BigIntersection.Spec (ImageFamily.Nonempty h𝒜)).2 ?_
  intro B hBfam
  rcases (ImageFamily.Spec).1 hBfam with ⟨A, hA𝒜, hBeq⟩
  subst hBeq
  refine (Image.Spec).2 ⟨x, ?_, hxy⟩
  exact (BigIntersection.Spec h𝒜).1 hxBI A hA𝒜

/-- [Enderton Ch3 §4, p.50] "Theorem 3K(b) ... Equality holds if `F` is single-rooted."
(Binary equality form.) -/
theorem thm_3Kb_image_inter_eq_of_single_rooted
    (F A B : Set) (hSR : IsSingleRooted F) :
    F⟦A ∩ B⟧ = F⟦A⟧ ∩ F⟦B⟧ := by
  apply extensionality
  intro y
  constructor
  · intro hy
    exact thm_3Kb_image_inter_subset F A B y hy
  · intro hy
    rcases (Intersection.Spec).1 hy with ⟨hyA, hyB⟩
    rcases (Image.Spec).1 hyA with ⟨x₁, hx₁A, hxy₁⟩
    rcases (Image.Spec).1 hyB with ⟨x₂, hx₂B, hxy₂⟩
    have hxEq : x₁ = x₂ := single_rooted_unique F x₁ x₂ y hSR hxy₁ hxy₂
    have hx₁B : x₁ ∈ B := by rw [hxEq]; exact hx₂B
    exact (Image.Spec).2 ⟨x₁, (Intersection.Spec).2 ⟨hx₁A, hx₁B⟩, hxy₁⟩

/-- [Enderton Ch3 §4, p.50] "Theorem 3K(b) ... Equality holds if `F` is single-rooted."
(Arbitrary-family equality form.) -/
theorem thm_3Kb_image_bigInter_eq_of_single_rooted
    (F 𝒜 : Set) (h𝒜 : 𝒜.Nonempty) (hSR : IsSingleRooted F) :
    F⟦BigIntersection 𝒜 h𝒜⟧
    = BigIntersection (ImageFamily F 𝒜) (ImageFamily.Nonempty h𝒜) := by
  apply extensionality
  intro y
  constructor
  · intro hy
    exact thm_3Kb_image_bigInter_subset F 𝒜 h𝒜 y hy
  · intro hy
    -- y belongs to every F⟦A⟧ for A ∈ 𝒜.
    have hAll : ∀ A, A ∈ 𝒜 → y ∈ F⟦A⟧ := by
      intro A hA𝒜
      have hFAfam : F⟦A⟧ ∈ ImageFamily F 𝒜 :=
        (ImageFamily.Spec).2 ⟨A, hA𝒜, rfl⟩
      exact (BigIntersection.Spec (ImageFamily.Nonempty h𝒜)).1 hy (F⟦A⟧) hFAfam
    -- Fix a base witness x₀ from some A₀ ∈ 𝒜 (without losing h𝒜).
    have hWit : ∃ A, A ∈ 𝒜 := h𝒜
    rcases hWit with ⟨A₀, hA₀⟩
    rcases (Image.Spec).1 (hAll A₀ hA₀) with ⟨x₀, _, hxy₀⟩
    refine (Image.Spec).2 ⟨x₀, ?_, hxy₀⟩
    refine (BigIntersection.Spec h𝒜).2 ?_
    intro A hA𝒜
    rcases (Image.Spec).1 (hAll A hA𝒜) with ⟨x, hxA, hxy⟩
    have hxEq : x = x₀ := single_rooted_unique F x x₀ y hSR hxy hxy₀
    rw [hxEq] at hxA
    exact hxA

/-- [Enderton Ch3 §4, p.50] "Theorem 3K ... (c) The image of a difference includes the
difference of the images: `F⟦A⟧ - F⟦B⟧ ⊆ F⟦A - B⟧`. Equality holds if `F` is
single-rooted." (Subset form.) -/
theorem thm_3Kc_image_diff_subset (F A B : Set) : F⟦A⟧ - F⟦B⟧ ⊆ F⟦A - B⟧ := by
  intro y hy
  rw [Difference.Spec, Image.Spec] at hy
  rcases hy with ⟨⟨x, hxA, hxy⟩, hyNotB⟩
  have hxNotB : x ∉ B := by
    intro hxB
    apply hyNotB
    exact (Image.Spec).2 ⟨x, hxB, hxy⟩
  exact (Image.Spec).2 ⟨x, (Difference.Spec).2 ⟨hxA, hxNotB⟩, hxy⟩

/-- [Enderton Ch3 §4, p.50] "Theorem 3K(c) ... Equality holds if `F` is single-rooted."
(Equality form.) -/
theorem thm_3Kc_image_diff_eq_of_single_rooted
    (F A B : Set) (hSR : IsSingleRooted F) :
    F⟦A⟧ - F⟦B⟧ = F⟦A - B⟧ := by
  apply extensionality
  intro y
  constructor
  · intro hy
    exact thm_3Kc_image_diff_subset F A B y hy
  · intro hy
    rcases (Image.Spec).1 hy with ⟨x, hxAB, hxy⟩
    rcases (Difference.Spec).1 hxAB with ⟨hxA, hxNotB⟩
    refine (Difference.Spec).2 ⟨?_, ?_⟩
    · exact (Image.Spec).2 ⟨x, hxA, hxy⟩
    · intro hyImgB
      rcases (Image.Spec).1 hyImgB with ⟨x', hx'B, hx'y⟩
      have hxEq : x = x' := single_rooted_unique F x x' y hSR hxy hx'y
      rw [hxEq] at hxNotB
      exact hxNotB hx'B

/-- [Enderton Ch3 §4, p.51] "Corollary 3L For any function `G` and sets `A`, `B`, and
`𝒜`: `G⁻¹⟦⋃𝒜⟧ = ⋃{G⁻¹⟦A⟧ | A ∈ 𝒜}`, `G⁻¹⟦⋂𝒜⟧ = ⋂{G⁻¹⟦A⟧ | A ∈ 𝒜}` for `𝒜 ≠ ∅`,
`G⁻¹⟦A - B⟧ = G⁻¹⟦A⟧ - G⁻¹⟦B⟧`."
(Helper: the inverse of a function is always single-rooted, by Theorem 3F.) -/
private lemma inverse_single_rooted_of_function
    {G : Set} (hG : IsFunction G) : IsSingleRooted (G⁻¹) :=
  (@thm_3F_relation_function_single_rooted G hG.1).1 hG

/-- [Enderton Ch3 §4, p.51] "Corollary 3L ... `G⁻¹⟦⋃𝒜⟧ = ⋃{G⁻¹⟦A⟧ | A ∈ 𝒜}`." -/
theorem cor_3La_inverse_image_bigUnion (G 𝒜 : Set) :
    (G⁻¹)⟦⋃ 𝒜⟧ = ⋃ (ImageFamily (G⁻¹) 𝒜) := by
  exact thm_3Ka_image_bigUnion (G⁻¹) 𝒜

/-- [Enderton Ch3 §4, p.51] "Corollary 3L ... `G⁻¹⟦⋂𝒜⟧ = ⋂{G⁻¹⟦A⟧ | A ∈ 𝒜}`
for `𝒜 ≠ ∅`." -/
theorem cor_3Lb_inverse_image_bigInter
    (G 𝒜 : Set) (hG : IsFunction G) (h𝒜 : 𝒜.Nonempty) :
    (G⁻¹)⟦BigIntersection 𝒜 h𝒜⟧
    = BigIntersection (ImageFamily (G⁻¹) 𝒜) (ImageFamily.Nonempty h𝒜) := by
  exact thm_3Kb_image_bigInter_eq_of_single_rooted (G⁻¹) 𝒜 h𝒜
    (inverse_single_rooted_of_function hG)

/-- [Enderton Ch3 §4, p.51] "Corollary 3L ... `G⁻¹⟦A - B⟧ = G⁻¹⟦A⟧ - G⁻¹⟦B⟧`." -/
theorem cor_3Lc_inverse_image_diff
    (G A B : Set) (hG : IsFunction G) :
    (G⁻¹)⟦A - B⟧ = (G⁻¹)⟦A⟧ - (G⁻¹)⟦B⟧ := by
  exact (thm_3Kc_image_diff_eq_of_single_rooted (G⁻¹) A B
    (inverse_single_rooted_of_function hG)).symm

/-- [Enderton Ch3 §4, p.51] "`⋃_{i ∈ I} F(i) = ⋃{F(i) | i ∈ I} = {x | x ∈ F(i) for
some i in I}`." Stated without preconditions (the set-theoretic definition makes
sense for any `F`, `I`). -/
noncomputable def IndexedUnion (F I : Set) : Set :=
  ⋃ (ran (Restriction F I))

-- When `I` is nonempty and `I ⊆ dom F`, the range of `F ↾ I` is nonempty.
lemma restriction_range_nonempty
    {F I : Set} (hI : I.Nonempty) (hDom : I ⊆ dom F) :
    (ran (Restriction F I)).Nonempty := by
  rcases hI with ⟨i, hi⟩
  rcases (Domain.Spec).1 (hDom i hi) with ⟨y, hxy⟩
  exact ⟨y, (Range.Spec).2 ⟨i, (Restriction.Pair.Spec).2 ⟨hxy, hi⟩⟩⟩

/-- [Enderton Ch3 §4, pp.51-52] "`⋂_{i ∈ I} F(i) = ⋂{F(i) | i ∈ I} = {x | x ∈ F(i) for
every i in I}`" (provided that `I` is nonempty). -/
noncomputable def IndexedIntersection
    (F I : Set) (hI : I.Nonempty) (hDom : I ⊆ dom F) : Set :=
  BigIntersection (ran (Restriction F I))
    (restriction_range_nonempty hI hDom)

/-- [Enderton Ch3 §4, p.52] "Call the set of all such functions `ᴬB`:
`ᴬB = {F | F is a function from A into B}`." -/
noncomputable def FunctionSpace (A B : Set) : Set :=
  Comprehension (fun G => MapsInto G A B) (𝒫 (A ⨯ B))

lemma FunctionSpace.Spec {A B G : Set} :
    G ∈ FunctionSpace A B ↔ G ⊆ (A ⨯ B) ∧ MapsInto G A B := by
  simp [FunctionSpace, Comprehension.Spec]


end Set
