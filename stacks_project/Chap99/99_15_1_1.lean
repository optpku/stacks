/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Spaces
universe u

/- 99.15.1.1: the category of families of curves is a full subcategory of
finite-presentation flat proper algebraic-space families. -/
@[stacks 0D50] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.inclusion :
  ∀ S : Scheme.{u}, Curves.Obj S ⥤ FpFlatProperGroupoids S)
