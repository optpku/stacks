/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.DimensionFunction

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.CohenMacaulay.dimensionFunction :
  (S : AlgebraicGeometry.Scheme.{u}) →
    [AlgebraicGeometry.Scheme.CohenMacaulay S] → S → ℤ)

#check (AlgebraicGeometry.Scheme.CohenMacaulay.dimensionFunction_apply :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.CohenMacaulay S] (s : S),
    AlgebraicGeometry.Scheme.CohenMacaulay.dimensionFunction S s =
      -(((ringKrullDim (S.presheaf.stalk s)).unbotD 0).toNat : ℤ))

#check (AlgebraicGeometry.Scheme.CohenMacaulay.instIsDimensionFunction :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.CohenMacaulay S],
    IsDimensionFunction (AlgebraicGeometry.Scheme.CohenMacaulay.dimensionFunction S))
