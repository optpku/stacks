/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth

/-!
# The structure morphism of the smooth-curve stack

The stack of smooth families of curves over a scheme is smooth over that scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of smooth families of curves is fibred in groupoids
over `Over S`. -/
instance instIsFiberedInGroupoids_smooth (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((smooth S).ι ⋙ p S) :=
  sorry

/-- The canonical structure morphism of the stack of smooth families of curves
over a scheme `S` is smooth over `S`. -/
instance instSmooth_smooth (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (smooth S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
