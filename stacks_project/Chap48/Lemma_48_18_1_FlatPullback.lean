/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback.Flat

@[expose] public section

open CategoryTheory

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.DerivedQCoh.Flat.pullbackPlusMapsTo :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (h : Y ⟶ X) [AlgebraicGeometry.Flat h],
    DerivedCategory.Plus.cohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.Plus.cohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty
          Y.toRingedSpace)).inverseImage
          (ExactFunctor.Derived.Plus.functor
            (RingedSpace.Hom.IsFlat.exactPullback h.toShHom)))

#check (AlgebraicGeometry.Scheme.DerivedQCoh.Flat.pullbackPlus :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (h : Y ⟶ X) [AlgebraicGeometry.Flat h],
    AlgebraicGeometry.Scheme.DerivedQCoh.Plus X ⥤
      AlgebraicGeometry.Scheme.DerivedQCoh.Plus Y)

#check (AlgebraicGeometry.Scheme.DerivedQCoh.Flat.pullbackPlus_toUnbounded_isomorphic :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (h : Y ⟶ X) [AlgebraicGeometry.Flat h],
    IsIsomorphic
      (AlgebraicGeometry.Scheme.DerivedQCoh.Flat.pullbackPlus h ⋙
        DerivedCategory.Plus.CohomologyIn.toUnbounded
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace))
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
        AlgebraicGeometry.Scheme.DerivedQCoh.pullback h))

#check (AlgebraicGeometry.Scheme.DerivedQCoh.Flat.pullbackPlusOfIsPullback :
  ∀ {X' X Y' Y : AlgebraicGeometry.Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [AlgebraicGeometry.Flat g] (sq : IsPullback g' f' f g),
    AlgebraicGeometry.Scheme.DerivedQCoh.Plus X ⥤
      AlgebraicGeometry.Scheme.DerivedQCoh.Plus X')
