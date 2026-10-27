/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Plus

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.Plus.ambient X :
  DerivedLQCohFbc.Plus X ⥤ ModuleDerived X)
#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.Plus.inclusion X :
  DerivedQCoh.Plus X ⥤ DerivedQCoh X)

end AlgebraicGeometry.AlgebraicStack
