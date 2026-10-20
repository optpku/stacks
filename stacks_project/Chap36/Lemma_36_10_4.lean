module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorDimension.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

/- Lemma 36.10.4 (1): the derived object associated to a complex of modules over an affine
scheme has Tor amplitude in `[a, b]` if and only if the original complex does. -/
@[stacks 08E9] #check (AlgebraicGeometry.tilde.hasTorAmplitudeIn_iff :
  ∀ (A : CommRingCat.{u})
    [DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (Spec A).toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat A)] (M : CochainComplex (ModuleCat A) ℤ) (a b : ℤ),
    RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) a b ↔
      DerivedCategory.DerivedTensor.HasTorAmplitudeIn (C := ModuleCat A) (DerivedCategory.Q.obj M) a b)

/- Lemma 36.10.4 (2): the derived object associated to a complex of modules over an affine
scheme has finite Tor dimension if and only if the original complex does. -/
@[stacks 08E9] #check (AlgebraicGeometry.tilde.hasFiniteTorDimension_iff :
  ∀ (A : CommRingCat.{u})
    [DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (Spec A).toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat A)] (M : CochainComplex (ModuleCat A) ℤ),
    RingedSpace.HasFiniteTorDimension
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) ↔
      DerivedCategory.DerivedTensor.HasFiniteTorDimension (C := ModuleCat A) (DerivedCategory.Q.obj M))
