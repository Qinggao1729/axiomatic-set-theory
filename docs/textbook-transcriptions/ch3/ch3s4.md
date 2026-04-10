# Ch3S4 Textbook Extraction (Functions, pp. 42-54)

## Items mapped to Lean

1. Function predicates
   - Set theory: function / into / onto / single-rooted.
   - Lean:
     - `def IsFunction (F : Set) : Prop`
     - `def MapsInto (F A B : Set) : Prop`
     - `def MapsOnto (F A B : Set) : Prop`
     - `def IsSingleRooted (R : Set) : Prop`
     - `def IsOneToOne (F : Set) : Prop`

2. Core constructions on relations
   - Set theory: identity, inverse, composition, restriction, image.
   - Lean:
     - `noncomputable def Identity (A : Set) : Set`
     - `noncomputable def Inverse (F : Set) : Set`
     - `noncomputable def Composition (F G : Set) : Set`
     - `noncomputable def Restriction (F C : Set) : Set`
     - `noncomputable def Image (F C : Set) : Set`
   - Spec lemmas use `...Spec` / `...Pair.Spec`.

3. Enderton 3E--3I core theorems in `S4`
   - 3E: domain/range of inverse; double inverse on relations.
   - 3F: inverse-function iff single-rooted.
   - 3G: inverse evaluation laws for one-to-one functions.
   - 3H: composition of functions; composition domain characterization.
   - 3I: `(F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹`.

4. Image and inverse-image laws
   - Lean:
     - `image_union`, `image_inter_subset`, `image_diff_subset`
     - `inverse_image_union`, `inverse_image_inter`, `inverse_image_diff`

5. Additional section-level definitions in `S4`
   - `GraphOn`, `GraphOn.mapsInto`
   - `IndexedUnion`, `IndexedIntersection`
   - `FunctionSpace`, `FunctionSpace.Spec`

6. Cross-file linkage for section-4 textbook content
   - 3J(a), 3J(b): `Set/Ch3/S5_InfiniteCartesianProducts.lean`
   - choice-first-form statement: `Set/Choice.lean`
