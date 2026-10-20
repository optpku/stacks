/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Normalized

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.hom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X),
    s.source ⟶ X)
