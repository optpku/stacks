/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Orbit

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.pointsOrbit :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
      PreRelation U → Points U.left → Set (Points U.left))
