/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Category

universe u

#check (AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    (I : AlgebraicGeometry.AlgebraicSpace.IdealSubobject X), Type (u + 1))
