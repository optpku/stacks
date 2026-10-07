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
    (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat A) ℤ) (a b : ℤ) :
    RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) a b ↔
      DerivedCategory.HasTorAmplitudeIn A (DerivedCategory.Q.obj M) a b := sorry

/-- The derived affine tilde object of a module complex has finite Tor dimension exactly
when the original complex has finite Tor dimension. -/
theorem hasFiniteTorDimension_iff
    (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat A) ℤ) :
    RingedSpace.HasFiniteTorDimension
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) ↔
      DerivedCategory.HasFiniteTorDimension A (DerivedCategory.Q.obj M) := sorry

/-- Derived restriction of an affine tilde complex along a ring morphism has Tor amplitude
in an interval exactly when the original complex has relative Tor amplitude in that interval. -/
theorem relativeRestriction_hasTorAmplitudeIn_iff
    (R A : CommRingCat.{u}) (φ : R ⟶ A)
    (M : CochainComplex (ModuleCat A) ℤ) (a b : ℤ) :
    RingedSpace.HasTorAmplitudeIn
        ((RingedSpace.ModuleDerived.relativeRestriction
          (Spec.map φ).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M))) a b ↔
      DerivedCategory.HasTorAmplitudeInAlong φ.hom (DerivedCategory.Q.obj M) a b := sorry

/-- Derived restriction of an affine tilde complex along a ring morphism locally has finite
Tor dimension exactly when the original complex has finite relative Tor dimension. -/
theorem relativeRestriction_locallyHasFiniteTorDimension_iff
    (R A : CommRingCat.{u}) (φ : R ⟶ A)
    (M : CochainComplex (ModuleCat A) ℤ) :
    RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
        ((RingedSpace.ModuleDerived.relativeRestriction
          (Spec.map φ).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M))) ↔
      DerivedCategory.HasFiniteTorDimensionAlong φ.hom (DerivedCategory.Q.obj M) := sorry

end AlgebraicGeometry.tilde
