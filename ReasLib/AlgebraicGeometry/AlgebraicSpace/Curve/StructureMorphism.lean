/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation

/-!
# The structure morphism of the stack of curves

The canonical structure morphism of the stack of curves over a scheme is
quasi-separated and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The canonical structure morphism of the stack of curves over a scheme is
quasi-separated. -/
instance instQuasiSeparated_toIdentitySlice (S : Scheme.{u}) :
    CohStack.Hom.QuasiSeparated (CohStack.toIdentitySlice (toGroupoids S)) := sorry

/-- The canonical structure morphism of the stack of curves over a scheme is
locally of finite presentation. -/
instance instLocallyOfFinitePresentation_toIdentitySlice (S : Scheme.{u}) :
    CohStack.Hom.LocallyOfFinitePresentation
      (CohStack.toIdentitySlice (toGroupoids S)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
