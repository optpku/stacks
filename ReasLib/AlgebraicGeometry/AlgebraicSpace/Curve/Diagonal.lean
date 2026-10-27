/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# The diagonal of the stack of curves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object diagonal of the category fibred in groupoids of families of curves
over a scheme is separated on scheme-slice representations by algebraic spaces. -/
theorem has_separated_diagonal (S : Scheme.{u}) :
    CohStack.Hom.has (@AlgebraicSpace.Separated S)
      (CohStack.diagonal (toGroupoids S)) := sorry

/-- The object diagonal of the category fibred in groupoids of families of curves
over a scheme is of finite presentation. -/
instance instFinitePresentation_diagonal (S : Scheme.{u}) :
    CohStack.Hom.FinitePresentation (CohStack.diagonal (toGroupoids S)) := sorry

/-- The diagonal of the category fibred in groupoids of families of curves
over a scheme is representable by algebraic spaces. -/
@[stacks 0D53]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal (S : Scheme.{u}) :
    AlgebraicGeometry.GroupScheme.Classifying.relativelyRepresentableByAlgebraicSpaces
      (CohStack.diagonal (toGroupoids S)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
