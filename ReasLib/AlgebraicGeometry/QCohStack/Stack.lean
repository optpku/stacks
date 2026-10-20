/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.QCohStack
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.QCohStack

/-- The projection from quasi-coherent sheaves over a scheme to its fppf site is fibered,
its fiber Hom-presheaves are sheaves, and its descent data are effective. -/
@[stacks 03YM]
instance instIsStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p S) :=
  sorry

end AlgebraicGeometry.QCohStack
