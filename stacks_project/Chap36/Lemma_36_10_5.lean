module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorDimension.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 36.10.5 (1): the affine tilde object associated to an `A`-module complex has
Tor-amplitude in `[a, b]` over the inverse-image structure sheaf if and only if the complex,
derived-restricted along `R ⟶ A`, has Tor-amplitude in `[a, b]` over `R`. -/
@[stacks 0DHY] #check (AlgebraicGeometry.tilde.relativeRestriction_hasTorAmplitudeIn_iff :
  ∀ (R A : CommRingCat.{u}) (φ : R ⟶ A)
    [DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom))]
    [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat R)]
    (M : CochainComplex (ModuleCat A) ℤ) (a b : ℤ),
    RingedSpace.HasTorAmplitudeIn
        ((RingedSpace.ModuleDerived.relativeRestriction
          (Spec.map φ).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M))) a b ↔
      DerivedCategory.DerivedTensor.HasTorAmplitudeIn (C := ModuleCat R)
        ((ModuleCat.derivedRestrictionOfScalars φ.hom).obj (DerivedCategory.Q.obj M)) a b)

/- Lemma 36.10.5 (2): the affine tilde object associated to an `A`-module complex locally has
finite Tor dimension over the inverse-image structure sheaf if and only if the complex,
derived-restricted along `R ⟶ A`, has finite Tor dimension over `R`. -/
@[stacks 0DHY] #check
  (AlgebraicGeometry.tilde.relativeRestriction_locallyHasFiniteTorDimension_iff :
    ∀ (R A : CommRingCat.{u}) (φ : R ⟶ A)
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom).restrict U.isOpenEmbedding))]
      [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat R)]
      (M : CochainComplex (ModuleCat A) ℤ),
    RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
        (X := RingedSpace.Hom.inverseImageBase (Spec.map φ).toShHom)
        ((RingedSpace.ModuleDerived.relativeRestriction
          (Spec.map φ).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M))) ↔
      DerivedCategory.DerivedTensor.HasFiniteTorDimension (C := ModuleCat R)
        ((ModuleCat.derivedRestrictionOfScalars φ.hom).obj (DerivedCategory.Q.obj M)))
