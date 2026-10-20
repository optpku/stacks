/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison

@[expose] public section

open CategoryTheory

noncomputable section

universe u

#check
  (AlgebraicGeometry.Scheme.QCoh.Derived.ringedSpaceHasDerivedCategory :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      HasDerivedCategory
        (AlgebraicGeometry.RingedSpace.QCoh X.toRingedSpace))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.comparison :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      DerivedCategory (AlgebraicGeometry.Scheme.QCoh X) ⥤
        DerivedCategory.CohomologyIn
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.comparison.compInclusion_isomorphic :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X ⋙
          (DerivedCategory.cohomologyIn
            (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι)
        ((AlgebraicGeometry.Scheme.QCoh.ringedSpaceEquivalence X).mapDerivedCategory.functor ⋙
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty
            X.toRingedSpace).ι.mapDerivedCategory))
