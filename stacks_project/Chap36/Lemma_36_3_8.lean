/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.3.8 (1): derived pullback along a morphism of schemes preserves
quasi-coherent cohomology. -/
@[stacks 08DW] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullback.mapsTo :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
      DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).inverseImage
            (RingedSpace.modulePullbackDerived f.toLRSHom.toShHom))

/- Lemma 36.3.8 (2): for a ring map `φ : A ⟶ B`, derived extension of scalars
`-⊗ᴸ_A B` and derived pullback along `Spec.map φ` commute, up to natural isomorphism,
with the affine equivalences from module-derived categories to `D_QCoh`. -/
@[stacks 08DW] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affinePullbackIso :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B)
        [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)]
        [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)],
      ModuleCat.derivedExtensionOfScalars φ.hom ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.affineFunctor B ≅
        AlgebraicGeometry.Scheme.DerivedQCoh.affineFunctor A ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.pullback (Spec.map φ))
