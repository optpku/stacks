/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Descent

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ResolutionDescent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X], Type (u + 1))
