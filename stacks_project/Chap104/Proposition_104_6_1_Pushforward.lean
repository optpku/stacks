/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Pushforward

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

variable [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]

#check (AlgebraicGeometry.AlgebraicStack.moduleDerivedPushforward f :
  ModuleDerived X ⥤ ModuleDerived Y)
#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.pushforward f :
  DerivedQCoh.Plus X ⥤ DerivedQCoh.Plus Y)

end AlgebraicGeometry.AlgebraicStack
