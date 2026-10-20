/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Diagonal biproduct functors

For a fixed indexing type `J`, this file packages the biproduct of a constant `J`-indexed
family as an endofunctor.  The hypotheses are deliberately objectwise: only the constant
biproducts used by the construction are required.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Limits.biproduct

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (J : Type w) [∀ X : C, HasBiproduct (fun _ : J ↦ X)]

/-- The diagonal map on a constant biproduct preserves identity morphisms. -/
@[stacks 0190 "identity map on a constant coefficient biproduct"]
theorem diagonal.map_id (X : C) :
    biproduct.map (fun _ : J ↦ 𝟙 X) =
      𝟙 (⨁ fun _ : J ↦ X) := sorry

/-- The diagonal map on a constant biproduct preserves composition. -/
@[stacks 0190 "composition of maps on constant coefficient biproducts"]
theorem diagonal.map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    biproduct.map (fun _ : J ↦ f ≫ g) =
      biproduct.map (fun _ : J ↦ f) ≫
        biproduct.map (fun _ : J ↦ g) := sorry

/-- The endofunctor taking an object to the biproduct of a constant `J`-indexed family. -/
@[stacks 0190 "constant coefficient biproduct functor"]
noncomputable def diagonal : C ⥤ C where
  obj X := ⨁ fun _ : J ↦ X
  map f := biproduct.map fun _ ↦ f
  map_id X := diagonal.map_id J X
  map_comp f g := diagonal.map_comp J f g

/-- The diagonal biproduct functor has the expected object value. -/
@[simp, stacks 0190 "constant coefficient biproduct object formula"]
theorem diagonal_obj (X : C) :
    (diagonal J).obj X = ⨁ fun _ : J ↦ X := sorry

/-- The diagonal biproduct functor acts componentwise on morphisms. -/
@[simp, stacks 0190 "constant coefficient biproduct map formula"]
theorem diagonal_map {X Y : C} (f : X ⟶ Y) :
    (diagonal J).map f = biproduct.map (fun _ : J ↦ f) := sorry

/-- A morphism commutes with every inclusion into a constant biproduct. -/
@[stacks 0190 "naturality of a constant coefficient biproduct inclusion"]
theorem diagonal.ι_naturality {K : Type w}
    [∀ X : C, HasBiproduct (fun _ : K ↦ X)]
    (i : K) {X Y : C} (f : X ⟶ Y) :
    f ≫ biproduct.ι (fun _ : K ↦ Y) i =
      biproduct.ι (fun _ : K ↦ X) i ≫ (diagonal K).map f := sorry

/-- Inclusion of one fixed summand, natural in the repeated object. -/
@[stacks 0190 "natural inclusion into a constant coefficient biproduct"]
noncomputable def diagonal.ι {K : Type w}
    [∀ X : C, HasBiproduct (fun _ : K ↦ X)] (i : K) :
    𝟭 C ⟶ diagonal K where
  app X := biproduct.ι (fun _ : K ↦ X) i
  naturality _ _ f := diagonal.ι_naturality i f

/-- A component of the natural inclusion is the corresponding biproduct inclusion. -/
@[simp, stacks 0190 "component of a constant coefficient biproduct inclusion"]
theorem diagonal.ι_app {K : Type w}
    [∀ X : C, HasBiproduct (fun _ : K ↦ X)] (i : K) (X : C) :
    (diagonal.ι i).app X =
      biproduct.ι (fun _ : K ↦ X) i := sorry

/-- Every projection from a constant biproduct commutes with a morphism. -/
@[stacks 0190 "naturality of a constant coefficient biproduct projection"]
theorem diagonal.π_naturality {K : Type w}
    [∀ X : C, HasBiproduct (fun _ : K ↦ X)]
    (i : K) {X Y : C} (f : X ⟶ Y) :
    (diagonal K).map f ≫ biproduct.π (fun _ : K ↦ Y) i =
      biproduct.π (fun _ : K ↦ X) i ≫ f := sorry

/-- Projection onto one fixed factor, natural in the repeated object. -/
@[stacks 0190 "natural projection from a constant coefficient biproduct"]
noncomputable def diagonal.π {K : Type w}
    [∀ X : C, HasBiproduct (fun _ : K ↦ X)] (i : K) :
    diagonal K ⟶ 𝟭 C where
  app X := biproduct.π (fun _ : K ↦ X) i
  naturality _ _ f := diagonal.π_naturality i f

/-- A component of the natural projection is the corresponding biproduct projection. -/
@[simp, stacks 0190 "component of a constant coefficient biproduct projection"]
theorem diagonal.π_app {K : Type w}
    [∀ X : C, HasBiproduct (fun _ : K ↦ X)] (i : K) (X : C) :
    (diagonal.π i).app X =
      biproduct.π (fun _ : K ↦ X) i := sorry

end CategoryTheory.Limits.biproduct
