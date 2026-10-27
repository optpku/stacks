/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor.Canonical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal

/-! # Tensor-pushforward base change for relatively flat complexes -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The canonical tensor-pushforward base-change morphism uses derived pullback on the
left tensor factor and ordinary termwise pullback on the right complex. -/
noncomputable def tensorPushforwardBaseChange
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ) :
    (ModuleDerived.pullback g).obj
        ((Modules.moduleDerivedPushforward f).obj
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        (DerivedTensor.Right.obj
          ((ModuleDerived.pullback g').obj E.obj)
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))) :=
  (DerivedBaseChange.map
      (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f')
      (cohomologyBaseChangeCartesianIso sq)).app
      (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
    (Modules.moduleDerivedPushforward f').map
      ((ModuleDerived.pullbackTensorIso g' E.obj (DerivedCategory.Q.obj G)).hom ≫
        (DerivedTensor.Bifunctor.Right.isoAppOf
          ((ModuleDerived.pullback g').obj (DerivedCategory.Q.obj G))
          (Modules.hasDerivedTensorRightCompatible X' _)
          ((ModuleDerived.pullback g').obj E.obj)).hom ≫
        (DerivedTensor.Bifunctor.leftFunctor (C := X'.Modules)
          ((ModuleDerived.pullback g').obj E.obj)).map
            ((ModuleDerived.pullbackCochainCounit g').app G) ≫
        (DerivedTensor.Bifunctor.Right.isoAppOf
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))
          (Modules.hasDerivedTensorRightCompatible X' _)
          ((ModuleDerived.pullback g').obj E.obj)).inv)

/-- The canonical tensor-pushforward comparison is the base-change mate followed by the
pushed-forward native tensor comparison and covariance along the ordinary-pullback counit. -/
theorem tensorPushforwardBaseChange_eq
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ) :
    tensorPushforwardBaseChange g' f' f g sq E G =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
        (Modules.moduleDerivedPushforward f').map
          ((ModuleDerived.pullbackTensorIso g' E.obj (DerivedCategory.Q.obj G)).hom ≫
            (DerivedTensor.Bifunctor.Right.isoAppOf
              ((ModuleDerived.pullback g').obj (DerivedCategory.Q.obj G))
              (Modules.hasDerivedTensorRightCompatible X' _)
              ((ModuleDerived.pullback g').obj E.obj)).hom ≫
            (DerivedTensor.Bifunctor.leftFunctor (C := X'.Modules)
              ((ModuleDerived.pullback g').obj E.obj)).map
                ((ModuleDerived.pullbackCochainCounit g').app G) ≫
            (DerivedTensor.Bifunctor.Right.isoAppOf
              (DerivedCategory.Q.obj
                (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))
              (Modules.hasDerivedTensorRightCompatible X' _)
              ((ModuleDerived.pullback g').obj E.obj)).inv) := rfl

/-- For a quasi-compact and quasi-separated morphism of algebraic spaces, derived pushforward
of a quasi-coherent derived object tensored with a bounded-above, degreewise quasi-coherent
complex flat over the target commutes with arbitrary base change. The right-hand complex
is pulled back termwise. -/
theorem pushforwardTensorBaseChange_isIso
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x) :
    IsIso (tensorPushforwardBaseChange g' f' f g sq E G) :=
  sorry

/-- The canonical tensor-pushforward comparison is invertible when boundedness, degreewise
quasi-coherence and relative flatness are available as proof instances. -/
instance tensorPushforwardBaseChange_isIso
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ)
    [Fact (CochainComplex.minus (Modules X) G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [Fact (∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x)] :
    IsIso (tensorPushforwardBaseChange g' f' f g sq E G) :=
  pushforwardTensorBaseChange_isIso g' f' f g sq E G
    (Fact.out : CochainComplex.minus (Modules X) G)
    (fun n ↦ inferInstanceAs (G.X n).IsQuasicoherent)
    (Fact.out : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x)

/-- A tensor-pushforward comparison presented using explicit ambient monoidal tensor models.
It composes the base-change mate with the model identifications, monoidal pullback comparison
and ordinary-pullback counit. -/
noncomputable def tensorPushforwardBaseChangeMap
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ) :
    (ModuleDerived.pullback g).obj
        ((Modules.moduleDerivedPushforward f).obj
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        (DerivedTensor.Right.obj
          ((ModuleDerived.pullback g').obj E.obj)
          (DerivedCategory.Q.obj
            (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))) :=
  (DerivedBaseChange.map
      (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f')
      (cohomologyBaseChangeCartesianIso sq)).app
      (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
    (Modules.moduleDerivedPushforward f').map
      ((ModuleDerived.pullback g').map
          (T_X.objIsoTensor E.obj (DerivedCategory.Q.obj G)).hom ≫
        (Functor.Monoidal.μIso (ModuleDerived.pullback g')
            E.obj (DerivedCategory.Q.obj G)).symm.hom ≫
          (𝟙 ((ModuleDerived.pullback g').obj E.obj) ⊗ₘ
            (ModuleDerived.pullbackCochainCounit g').app G) ≫
            (T_X'.objIsoTensor ((ModuleDerived.pullback g').obj E.obj)
              (DerivedCategory.Q.obj
                (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G))).inv)

/-- The model-dependent tensor-pushforward comparison is the base-change mate followed by
the pushed-forward ambient tensor comparisons and the ordinary-pullback counit. -/
theorem tensorPushforwardBaseChangeMap_eq
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g)
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ) :
    tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X' E G =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
        (Modules.moduleDerivedPushforward f').map
          ((ModuleDerived.pullback g').map
              (T_X.objIsoTensor E.obj (DerivedCategory.Q.obj G)).hom ≫
            (Functor.Monoidal.μIso (ModuleDerived.pullback g')
                E.obj (DerivedCategory.Q.obj G)).symm.hom ≫
              (𝟙 ((ModuleDerived.pullback g').obj E.obj) ⊗ₘ
                (ModuleDerived.pullbackCochainCounit g').app G) ≫
                (T_X'.objIsoTensor ((ModuleDerived.pullback g').obj E.obj)
                  (DerivedCategory.Q.obj
                    (((Modules.pullback g').mapHomologicalComplex
                      (up ℤ)).obj G))).inv) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
