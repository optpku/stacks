/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Impurity
import StacksCheckRecall
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  [FiniteType f] [Decent f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
  (y : |Y|)

/- Definition 77.2.2: a diagram 77.2.1.1 is an impurity of `ℱ` above `y` when `ξ`
lies in the relative assassin of `ℱ` after base change to `T` and `t` is not in
the image of the closure of `{ξ}` under `f_T`. -/
@[stacks 0CV8] #check (AlgebraicGeometry.AlgebraicSpace.Modules.Impurity ℱ f y : Type (u + 1))

end
