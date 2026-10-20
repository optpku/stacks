module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.tilde

/-- The derived affine tilde object of a module complex has Tor amplitude in an interval
exactly when the original complex has Tor amplitude in that interval. -/
theorem hasTorAmplitudeIn_iff
    (A : CommRingCat.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules (Spec A).toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat A)]
    (M : CochainComplex (ModuleCat A) ℤ) (a b : ℤ) :
    RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) a b ↔
      DerivedCategory.DerivedTensor.HasTorAmplitudeIn (C := ModuleCat A) (DerivedCategory.Q.obj M) a b := sorry

/-- The derived affine tilde object of a module complex has finite Tor dimension exactly
when the original complex has finite Tor dimension. -/
theorem hasFiniteTorDimension_iff
    (A : CommRingCat.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules (Spec A).toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat A)]
    (M : CochainComplex (ModuleCat A) ℤ) :
    RingedSpace.HasFiniteTorDimension
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) ↔
      DerivedCategory.DerivedTensor.HasFiniteTorDimension (C := ModuleCat A) (DerivedCategory.Q.obj M) := sorry

/-- Derived restriction of an affine tilde complex along a ring morphism has Tor amplitude
in an interval exactly when the original complex has relative Tor amplitude in that interval. -/
theorem relativeRestriction_hasTorAmplitudeIn_iff
    (R A : CommRingCat.{u}) (φ : R ⟶ A)
    [DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom))]
    [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat R)]
    (M : CochainComplex (ModuleCat A) ℤ) (a b : ℤ) :
    RingedSpace.HasTorAmplitudeIn
        ((RingedSpace.ModuleDerived.relativeRestriction
          (Spec.map φ).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M))) a b ↔
      DerivedCategory.DerivedTensor.HasTorAmplitudeIn (C := ModuleCat R)
        ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars φ.hom).obj
          (DerivedCategory.Q.obj M)) a b := sorry

/-- Derived restriction of an affine tilde complex along a ring morphism locally has finite
Tor dimension exactly when the original complex has finite relative Tor dimension. -/
theorem relativeRestriction_locallyHasFiniteTorDimension_iff
    (R A : CommRingCat.{u}) (φ : R ⟶ A)
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom).restrict U.isOpenEmbedding))]
    [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat R)]
    (M : CochainComplex (ModuleCat A) ℤ) :
    RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
        (X := RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom)
        ((RingedSpace.ModuleDerived.relativeRestriction
          (Spec.map φ).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M))) ↔
      DerivedCategory.DerivedTensor.HasFiniteTorDimension (C := ModuleCat R)
        ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars φ.hom).obj
          (DerivedCategory.Q.obj M)) := sorry

end AlgebraicGeometry.tilde
