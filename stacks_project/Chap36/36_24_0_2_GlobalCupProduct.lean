/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.GlobalCupProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Kunneth

/- Compatibility check for the generic global cup-product construction. -/
#check (AlgebraicGeometry.Scheme.Modules.Kunneth.globalCupProduct :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis (coefficientSite a))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (coefficientPushforwardHom b))
      (RingedSite.Hom.ModuleQis (coefficientSite b))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite (pullback.fst a b ≫ a)))]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)]
    (globalSections : CoefficientGlobalSections S)
    (coefficientDerivedTensor :
      CoefficientDerived (𝟙 S) ⥤ CoefficientDerived (𝟙 S) ⥤ CoefficientDerived (𝟙 S))
    (model : CoefficientGlobalTensorModel S globalSections coefficientDerivedTensor)
    (relativeCupProduct :
      ((coefficientDerivedTensor.obj
          ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom a)).obj
            (coefficientObject a F))).obj
        ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom b)).obj
          (coefficientObject b G))) ⟶
        (RingedSite.Hom.modulePushforwardDerived (fiberCoefficientHom a b)).obj
          (externalTotal a b T hT F G)),
    ((AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor.globalSectionsCurried
        S.toRingedSpace).obj (derivedGlobalSections a globalSections F)).obj
        (derivedGlobalSections b globalSections G) ⟶
      totalDerivedGlobalSections a b T hT globalSections F G)

end
