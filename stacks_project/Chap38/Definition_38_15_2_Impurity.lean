/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (s : S)

#check (Impurity F f s : Type (u + 1))

end AlgebraicGeometry.Scheme.Modules
