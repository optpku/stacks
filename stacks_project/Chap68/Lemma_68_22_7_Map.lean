/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Birational

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.IsBirational.exists_normalizationMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [IsDecent X] [IsDecent Y]
      [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
      (f : X ⟶ Y) [IsBirational f],
      ∃ g : X.normalization ⟶ Y.normalization,
        g ≫ Y.normalizationTo = X.normalizationTo ≫ f ∧ IsBirational g)
