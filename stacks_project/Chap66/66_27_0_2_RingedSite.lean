/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Spaces

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spacesStructureSheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.Sheaf (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology X) RingCat.{u})
