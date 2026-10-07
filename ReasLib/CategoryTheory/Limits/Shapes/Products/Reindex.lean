module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing constant products

For a fixed indexing type, taking a product of copies of an object is functorial in that object.
A function of indexing types induces the contravariant reindexing natural transformation.  This
is the categorical product-projection API used by finite coskeleton calculations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w' w v u

namespace CategoryTheory.Limits.Power

variable {C : Type u} [Category.{v} C]

/-- Apply a morphism to every factor of a constant product. -/
noncomputable def map (S : Type w) [HasProductsOfShape S C]
    {X Y : C} (f : X ⟶ Y) :
    (∏ᶜ fun _ : S ↦ X) ⟶ (∏ᶜ fun _ : S ↦ Y) :=
  Pi.map (fun _ ↦ f)

/-- Constant-product maps preserve identities. -/
theorem map_id (S : Type w) [HasProductsOfShape S C] (X : C) :
    map S (𝟙 X) = 𝟙 (∏ᶜ fun _ : S ↦ X) := sorry

/-- Constant-product maps preserve composition. -/
theorem map_comp (S : Type w) [HasProductsOfShape S C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map S (f ≫ g) = map S f ≫ map S g := sorry

/-- The functor taking an object to its `S`-indexed power. -/
@[stacks 01GJ "constant product functor"]
noncomputable def functor (S : Type w) [HasProductsOfShape S C] : C ⥤ C where
  obj X := ∏ᶜ fun _ : S ↦ X
  map f := map S f
  map_id X := map_id S X
  map_comp f g := map_comp S f g

/-- The component of contravariant power reindexing along `tau : S' → S`. -/
noncomputable def reindexApp {S : Type w} {S' : Type w'}
    [HasProductsOfShape S C] [HasProductsOfShape S' C]
    (tau : S' → S) (X : C) :
    (functor (C := C) S).obj X ⟶ (functor (C := C) S').obj X :=
  Pi.lift (fun s' ↦ Pi.π (fun _ : S ↦ X) (tau s'))

/-- Power reindexing is natural in the repeated object. -/
theorem reindexApp_naturality {S : Type w} {S' : Type w'}
    [HasProductsOfShape S C] [HasProductsOfShape S' C]
    (tau : S' → S) {X Y : C} (f : X ⟶ Y) :
    (functor (C := C) S).map f ≫ reindexApp tau Y =
      reindexApp tau X ≫ (functor (C := C) S').map f := sorry

/-- A function `S' → S` induces the natural projection from `S`-indexed powers to
`S'`-indexed powers. -/
@[stacks 01GJ "constant product reindexing"]
noncomputable def reindex {S : Type w} {S' : Type w'}
    [HasProductsOfShape S C] [HasProductsOfShape S' C]
    (tau : S' → S) : functor (C := C) S ⟶ functor (C := C) S' where
  app X := reindexApp tau X
  naturality _ _ f := reindexApp_naturality tau f

/-- The component of `reindex tau` is the corresponding product projection. -/
@[simp]
theorem reindex_app {S : Type w} {S' : Type w'}
    [HasProductsOfShape S C] [HasProductsOfShape S' C]
    (tau : S' → S) (X : C) :
    (reindex (C := C) tau).app X = reindexApp tau X := sorry

/-- Reindexing followed by projection at `s'` is projection at `tau s'`. -/
@[reassoc (attr := simp)]
theorem reindex_π {S : Type w} {S' : Type w'}
    [HasProductsOfShape S C] [HasProductsOfShape S' C]
    (tau : S' → S) (X : C) (s' : S') :
    (reindex (C := C) tau).app X ≫ Pi.π (fun _ : S' ↦ X) s' =
      Pi.π (fun _ : S ↦ X) (tau s') := sorry

end CategoryTheory.Limits.Power
