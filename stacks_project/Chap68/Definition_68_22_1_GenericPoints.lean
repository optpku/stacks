/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints

#check (AlgebraicGeometry.AlgebraicSpace.genericPoints :
  {S : AlgebraicGeometry.Scheme} → (X : AlgebraicGeometry.AlgebraicSpace S) →
    Set (AlgebraicGeometry.AlgebraicSpace.Points X))
