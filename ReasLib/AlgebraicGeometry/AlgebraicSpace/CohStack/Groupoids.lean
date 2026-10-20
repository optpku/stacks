/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory

/-!
# The groupoid fibration of coherent sheaves

The projection from finitely presented flat modules with proper support on
scheme-valued fibers is fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a finite-presentation morphism `f : X ⟶ B`, the projection from finitely
presented quasi-coherent modules on its scheme-valued fibers, flat over the test
scheme with proper support, to `Over S` is fibred in groupoids. -/
instance instIsFiberedInGroupoids (f : X ⟶ B) [FinitePresentation f] :
    Functor.IsFibered.InGroupoids (p f) := sorry

/-- The category of finitely presented quasi-coherent modules with proper
support on the fibres of `f`, flat over the test scheme, bundled as a category
fibred in groupoids over `Over S`, with Hom-universe `u + 1`. -/
def toGroupoids (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f)

/-- The projection of `toGroupoids f` is `p f`, sending `(T, g, F)` to `T`. -/
theorem toGroupoids_p (f : X ⟶ B) [FinitePresentation f] :
    (toGroupoids f).p = p f := sorry

/-- The total category of `toGroupoids f` is the category `Obj f` of finitely
presented modules on scheme-valued fibers, flat over the test scheme with proper
support. -/
theorem toGroupoids_total (f : X ⟶ B) [FinitePresentation f] :
    (toGroupoids f).total = Obj f := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
