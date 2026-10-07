module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
# Diagonal product functors

For a fixed indexing type `J`, this file packages the product of a constant `J`-indexed
family as an endofunctor.  It assumes only the constant products used by the construction,
rather than products of every `J`-indexed family.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Limits.Pi

variable {C : Type u} [Category.{v} C]
variable (J : Type w) [∀ X : C, HasProduct (fun _ : J ↦ X)]

/-- The componentwise map on a constant product preserves identity morphisms. -/
@[stacks 0190 "identity map on a constant coefficient product"]
theorem diagonal.map_id (X : C) :
    Pi.map (fun _ : J ↦ 𝟙 X) =
      𝟙 (∏ᶜ fun _ : J ↦ X) := sorry

/-- The componentwise map on a constant product preserves composition. -/
@[stacks 0190 "composition of maps on constant coefficient products"]
theorem diagonal.map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Pi.map (fun _ : J ↦ f ≫ g) =
      Pi.map (fun _ : J ↦ f) ≫
        Pi.map (fun _ : J ↦ g) := sorry

/-- The endofunctor taking an object to the product of a constant `J`-indexed family. -/
@[stacks 0190 "constant coefficient product functor"]
noncomputable def diagonal : C ⥤ C where
  obj X := ∏ᶜ fun _ : J ↦ X
  map f := Pi.map fun _ ↦ f
  map_id X := diagonal.map_id J X
  map_comp f g := diagonal.map_comp J f g

/-- The diagonal product functor has the expected object value. -/
@[simp, stacks 0190 "constant coefficient product object formula"]
theorem diagonal_obj (X : C) :
    (diagonal J).obj X = ∏ᶜ fun _ : J ↦ X := sorry

/-- The diagonal product functor acts componentwise on morphisms. -/
@[simp, stacks 0190 "constant coefficient product map formula"]
theorem diagonal_map {X Y : C} (f : X ⟶ Y) :
    (diagonal J).map f = Pi.map (fun _ : J ↦ f) := sorry

/-- Every projection from a constant product commutes with a morphism. -/
@[stacks 0190 "naturality of a constant coefficient product projection"]
theorem diagonal.π_naturality {K : Type w}
    [∀ X : C, HasProduct (fun _ : K ↦ X)]
    (i : K) {X Y : C} (f : X ⟶ Y) :
    (diagonal K).map f ≫ Pi.π (fun _ : K ↦ Y) i =
      Pi.π (fun _ : K ↦ X) i ≫ f := sorry

/-- Projection onto one fixed factor, natural in the repeated object. -/
@[stacks 0190 "natural projection from a constant coefficient product"]
noncomputable def diagonal.π {K : Type w}
    [∀ X : C, HasProduct (fun _ : K ↦ X)] (i : K) :
    diagonal K ⟶ 𝟭 C where
  app X := Pi.π (fun _ : K ↦ X) i
  naturality _ _ f := diagonal.π_naturality i f

/-- A component of the natural projection is the corresponding product projection. -/
@[simp, stacks 0190 "component of a constant coefficient product projection"]
theorem diagonal.π_app {K : Type w}
    [∀ X : C, HasProduct (fun _ : K ↦ X)] (i : K) (X : C) :
    (diagonal.π i).app X =
      Pi.π (fun _ : K ↦ X) i := sorry

end CategoryTheory.Limits.Pi
