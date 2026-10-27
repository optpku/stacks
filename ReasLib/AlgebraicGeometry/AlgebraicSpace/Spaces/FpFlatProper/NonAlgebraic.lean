/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic

public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids

/-- The stack in groupoids of flat, proper, finitely presented algebraic spaces
over schemes, viewed over the terminal scheme `specZ`, is not an algebraic stack. -/
@[stacks 0D1R]
theorem not_isAlgebraic :
    ¬ CohStack.AlgebraicStack (toGroupoids specZ.{u}) := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
