/-
Copyright (c) 2026 ReasLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Detecting monoid-object morphisms on points

A map of monoid objects preserves the operations if its postcomposition maps
do so for every test object. The unit and the product of the source already
detect the two equations. This criterion applies to group schemes, internal
monoids, and representability constructions without geometric hypotheses.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.IsMonHom

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {M N : C} [MonObj M] [MonObj N]

/-- Pointwise preservation of the unit and multiplication detects a monoid-object morphism. -/
theorem of_pointwise (f : M ⟶ N)
    (h_one : ∀ X : C, (1 : X ⟶ M) ≫ f = 1)
    (h_mul : ∀ (X : C) (x y : X ⟶ M), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) :
    IsMonHom f where
  one_hom := by simpa [Hom.one_def] using h_one (𝟙_ C)
  mul_hom := by
    simpa [Hom.mul_def] using
      h_mul (M ⊗ M) (fst M M) (snd M M)

end CategoryTheory.IsMonHom
