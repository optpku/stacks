/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Category
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory

/-!
# The Picard category as a category fibred in groupoids
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard category of a morphism of algebraic spaces, bundled as a category
fibred in groupoids over `Over S`, with Hom-universe `u + 1`. -/
def toGroupoids (f : X ⟶ B) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f)

/-- The projection of the Picard groupoid fibration is the Picard projection. -/
theorem toGroupoids_p (f : X ⟶ B) : (toGroupoids f).p = p f := sorry

/-- The total category of the Picard groupoid fibration is the category of Picard objects. -/
theorem toGroupoids_total (f : X ⟶ B) : (toGroupoids f).total = Obj f := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
