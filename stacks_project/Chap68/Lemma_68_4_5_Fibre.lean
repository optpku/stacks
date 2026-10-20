/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.forallAffineEtaleFiniteAbove :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
