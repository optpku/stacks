/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.GlobalCupProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Kunneth

/- 36.24.0.2: The canonical global cup product
`RΓ(X, F) ⊗ᴸ_A RΓ(Y, G) ⟶ RΓ(X ×_S Y, Tot(F ⊠ G))` in `D(A)`, where
`A = Γ(S, ⊤)`, for finite-order differential-operator complexes `F` and `G`. -/
@[stacks 0FLR] #check
  (AlgebraicGeometry.Scheme.Modules.Kunneth.canonicalGlobalCupProduct :
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
          (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
      [Functor.HasLeftDerivedFunctor
        (RingedSite.Hom.modulePullbackToDerived.{u} (coefficientPushforwardHom b))
        (RingedSite.Hom.ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
      [Functor.HasLeftDerivedFunctor
        (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
        (RingedSite.Hom.ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
      [Functor.HasLeftDerivedFunctor
        (RingedSite.Hom.modulePullbackToDerived.{u} (rightFiberCoefficientHom a b))
        (RingedSite.Hom.ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
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
      [RelativeCupProduct.PullbackTensorTargetIsLeftDerived a b]
      (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
        Hom.FiniteOrderDifferentialOperatorCat b ⥤
          Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
      (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
      [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
      (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
      (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
      [HomologicalComplex.HasMapBifunctor F G T (up ℤ)]
      (globalSections : CoefficientGlobalSections S)
      (model : CoefficientGlobalTensorModel S globalSections
        (RelativeCupProduct.coefficientDerivedTensor (𝟙 S))),
      ((AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor.globalSectionsCurried
          S.toRingedSpace).obj (derivedGlobalSections a globalSections F)).obj
          (derivedGlobalSections b globalSections G) ⟶
        totalDerivedGlobalSections a b T hT globalSections F G)

end
