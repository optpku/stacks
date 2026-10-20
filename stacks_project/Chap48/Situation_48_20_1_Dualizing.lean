/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Dualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingComplex :
    ∀ {X : RingedSpace.{u}} (K : RingedSpace.ModuleDerived X)
      [MonoidalCategory (RingedSpace.ModuleDerived X)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X)), Prop)

#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingComplex.ofConditions :
    ∀ {X : RingedSpace.{u}} {K : RingedSpace.ModuleDerived X}
      [MonoidalCategory (RingedSpace.ModuleDerived X)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived X)},
      K.IsPseudoCoherent → DerivedCategory.HasFiniteInjectiveDimension K →
        IsIso (@MonoidalClosed.curry' (RingedSpace.ModuleDerived X) _ _ K K
          (H.closed K) (𝟙 K)) →
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingComplex K H)

#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.isDualizingComplex_iff :
    ∀ {X : RingedSpace.{u}} (K : RingedSpace.ModuleDerived X)
      [MonoidalCategory (RingedSpace.ModuleDerived X)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X)),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingComplex K H ↔
        K.IsPseudoCoherent ∧ DerivedCategory.HasFiniteInjectiveDimension K ∧
          IsIso (@MonoidalClosed.curry' (RingedSpace.ModuleDerived X) _ _ K K
            (H.closed K) (𝟙 K)))
