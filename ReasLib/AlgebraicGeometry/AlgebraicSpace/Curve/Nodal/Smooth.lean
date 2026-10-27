/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Nodal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth

/-!
# Smoothness of the structure morphism of nodal curves

The stack of nodal curves has smooth structure morphism over its base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of `𝒞urves` cut out by `nodal` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_nodal (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((nodal S).ι ⋙ p S) :=
  sorry

/-- The structure morphism of the stack of nodal curves over a scheme is smooth. -/
instance instSmooth_nodal (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (nodal S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
