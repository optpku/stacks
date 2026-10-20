/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.RelativeCupProduct
import stacks_project.Chap36.«36_24_0_1_RelativeCupProduct»

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.Scheme.Modules.Kunneth

noncomputable section

universe u

/- 36.24.0.1: the canonical relative cup-product morphism
`R(a)_* F ⊗ᴸ R(b)_* G ⟶ R(f)_* Tot(F ⊠ G)`. -/
@[stacks 0G4B] #check (AlgebraicGeometry.Scheme.RelativeCupProduct.map :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(coefficientPushforwardHom a).modulePushforward.IsRightAdjoint]
    [(coefficientPushforwardHom b).modulePushforward.IsRightAdjoint]
    [(fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightFiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis.{u}
        (AlgebraicGeometry.RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (coefficientPushforwardHom b))
      (RingedSite.Hom.ModuleQis.{u}
        (AlgebraicGeometry.RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u}
        (AlgebraicGeometry.RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (rightFiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u}
        (AlgebraicGeometry.RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (coefficientPushforwardHom b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (rightFiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (leftCoefficientHom a b)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (rightCoefficientHom a b)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (coefficientPushforwardHom a)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (coefficientPushforwardHom b)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (fiberCoefficientHom a b)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (rightFiberCoefficientHom a b)]
    [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
      (leftCoefficientHom a b) (coefficientPushforwardHom a))]
    [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
      (rightCoefficientHom a b) (coefficientPushforwardHom b))]
    [Functor.Monoidal
      (RingedSite.Hom.modulePullbackHomotopy.{u} (fiberCoefficientHom a b))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S)))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
    [AlgebraicGeometry.Scheme.RelativeCupProduct.PullbackTensorTargetIsLeftDerived a b]
    (T : AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat a ⥤
      AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat b ⥤
        AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat
          (pullback.fst a b ≫ a))
    (hT : AlgebraicGeometry.Scheme.Hom.IsExternalTensorProductFunctor a b
      (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex
      (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex
      (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)],
    ((AlgebraicGeometry.Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S)).obj
      ((RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom a)).obj
        (coefficientObject a F))).obj
      ((RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom b)).obj
        (coefficientObject b G)) ⟶
      (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj
        (externalTotal a b T hT F G))

end
