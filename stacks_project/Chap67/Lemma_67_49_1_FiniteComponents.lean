/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents

@[expose] public section

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.codimZeroPoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), Set (AlgebraicSpace.Points X))
