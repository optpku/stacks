/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Thickening

open AlgebraicGeometry CategoryTheory

universe u

#check
  (@AlgebraicGeometry.AlgebraicSpace.smallEtalePullback.isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
      [AlgebraicGeometry.AlgebraicSpace.IsThickening i]
      (hf : yoneda.relativelyRepresentable i),
      (AlgebraicGeometry.AlgebraicSpace.smallEtalePullback i hf).IsEquivalence)
