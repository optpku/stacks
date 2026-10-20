/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.Basic

universe u

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isDualizingComplex_iff :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X : AlgebraicGeometry.AlgebraicSpace S} →
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X] →
        (K : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X) →
          (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex K ↔
            AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.forallEtaleScheme K))
