module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.AdicLimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf

universe u

/- Lemma 52.2.1 (1) -/
@[stacks 0EI8] #check (AlgebraicGeometry.Scheme.Modules.AdicLimit.isOf :
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (F : SequentialInverseSystem X.Modules)
    [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1))),
    HomotopyLimit.IsOf
      (F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ))
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)))

/- Lemma 52.2.1 (2) -/
@[stacks 0EI8] #check (AlgebraicGeometry.Scheme.Modules.AdicLimit.higherCohomologyIsZero :
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (F : SequentialInverseSystem X.Modules)
    [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1)))
    (U : X.affineOpens) (p : ℕ) (hp : 0 < p),
    IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace (U : X.Opens)
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) (p : ℤ)))

/- Lemma 52.2.1 (3) -/
@[stacks 0EI8] #check (AlgebraicGeometry.Scheme.Modules.AdicLimit.cohomologyShortExact :
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (F : SequentialInverseSystem X.Modules)
    [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1))) (p : ℤ),
    ∃ (ι :
        SequentialInverseSystem.Milnor.ProductCone.canonicalR1
            (((F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ)) ⋙
              RingedSpace.moduleDerivedSectionsAtOpenToAb X.toRingedSpace ⊤) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} (p - 1)) ⟶
          RingedSpace.moduleOpenHypercohomology X.toRingedSpace ⊤
            ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) p)
      (π :
        RingedSpace.moduleOpenHypercohomology X.toRingedSpace ⊤
            ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (limit F)) p ⟶
          limit (((F ⋙ DerivedCategory.singleFunctor X.Modules (0 : ℤ)) ⋙
            RingedSpace.moduleDerivedSectionsAtOpenToAb X.toRingedSpace ⊤) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact)

/- Lemma 52.2.1 (4) -/
@[stacks 0EI8] #check (AlgebraicGeometry.Scheme.Modules.AdicLimit.stageComparison_isIso :
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (F : SequentialInverseSystem X.Modules)
    [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1)))
    (hI : I.IsFiniteType) (n : ℕ),
    IsIso (AlgebraicGeometry.Scheme.Modules.AdicLimit.stageComparison I F h_kernel n))

/- Lemma 52.2.1 (5) -/
@[stacks 0EI8] #check (AlgebraicGeometry.Scheme.Modules.AdicLimit.powerLimitComparison_isIso :
  ∀ {X : Scheme.{u}} (I : X.IdealSheafData) (F : SequentialInverseSystem X.Modules)
    [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1)))
    (hI : I.IsFiniteType) (n : ℕ),
    IsIso (AlgebraicGeometry.Scheme.Modules.AdicLimit.powerLimitComparison I F n))
