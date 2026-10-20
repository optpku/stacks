/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogPole.Boundary
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry RingedSite.Hom

noncomputable section

universe u

/- Lemma 50.15.5 (1) -/
@[stacks 0FUQ] #check
  (AlgebraicGeometry.Scheme.DeRham.LogPole.upperTriangle :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
      [IsEffectiveCartierDivisor i]
      (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i),
      AlgebraicGeometry.Scheme.DeRham.LogPole.restriction f i ≫
          AlgebraicGeometry.Scheme.DeRham.LogPole.boundary f i h_defined =
        AlgebraicGeometry.Scheme.DeRham.LogPole.negativeAction f i)

/- Lemma 50.15.5 (2) -/
@[stacks 0FUQ] #check
  (AlgebraicGeometry.Scheme.DeRham.LogPole.lowerTriangle :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
      [IsEffectiveCartierDivisor i]
      (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i),
      AlgebraicGeometry.Scheme.DeRham.LogPole.boundary f i h_defined ≫
          (shiftFunctor _ (2 : ℤ)).map
            (AlgebraicGeometry.Scheme.DeRham.LogPole.restriction f i) =
        AlgebraicGeometry.Scheme.DeRham.LogPole.restrictedAction f i)
