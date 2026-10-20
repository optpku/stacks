/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback

/-!
# Affine Derived Pullback

This module identifies derived pullback along a morphism of affine schemes with derived
extension of scalars on their coordinate rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Postcomposing the scalar-extension-first route by ambient inclusion only reassociates
functor composition. -/
noncomputable def affineExtensionInclusionIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)] :
    (ModuleCat.derivedExtensionOfScalars φ.hom ⋙ affineFunctor B) ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec B).toRingedSpace)).ι ≅
      ModuleCat.derivedExtensionOfScalars φ.hom ⋙
        (affineFunctor B ⋙
          (DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty (Spec B).toRingedSpace)).ι) :=
  Functor.associator _ _ _

/-- Postcomposing restricted affine pullback by ambient inclusion recovers ambient derived
module pullback. -/
noncomputable def affinePullbackInclusionIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    (affineFunctor A ⋙ pullback (Spec.map φ)) ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec B).toRingedSpace)).ι ≅
      (affineFunctor A ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι) ⋙
        RingedSpace.modulePullbackDerived (Spec.map φ).toLRSHom.toShHom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pullback.inclusionIso (Spec.map φ)) ≪≫
    (Functor.associator _ _ _).symm

/-- Derived extension of scalars followed by the affine presentation is naturally isomorphic
to the affine presentation followed by derived pullback. -/
noncomputable def affinePullbackIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)]
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)] :
    ModuleCat.derivedExtensionOfScalars φ.hom ⋙ affineFunctor B ≅
      affineFunctor A ⋙ pullback (Spec.map φ) :=
  ((DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty
      (Spec B).toRingedSpace)).fullyFaithfulι.whiskeringRight _).preimageIso
    (affineExtensionInclusionIso φ ≪≫ affinePullbackAmbientIso φ ≪≫
      (affinePullbackInclusionIso φ).symm)

end AlgebraicGeometry.Scheme.DerivedQCoh
