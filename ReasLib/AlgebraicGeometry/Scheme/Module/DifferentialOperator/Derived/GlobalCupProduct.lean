/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.RelativeCupProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth

/-- A realization of derived global sections for coefficient-module complexes on a scheme,
valued in the derived category of modules over its ring of global functions. -/
abbrev CoefficientGlobalSections (S : Scheme.{u}) :=
  CoefficientDerived (𝟙 S) ⥤ DerivedCategory (ModuleCat.{u} (Scheme.globalSectionsRing S))

/-- The derived global sections of a finite-order differential-operator complex,
represented through derived direct image to the base coefficient site. -/
noncomputable abbrev derivedGlobalSections {X S : Scheme.{u}} (a : X ⟶ S)
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis (coefficientSite a))]
    (globalSections : CoefficientGlobalSections S)
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ) :
    DerivedCategory (ModuleCat.{u} (Scheme.globalSectionsRing S)) :=
  globalSections.obj
    ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom a)).obj
      (coefficientObject a F))

/-- The derived global sections of the total external product of two
finite-order differential-operator complexes. -/
noncomputable abbrev totalDerivedGlobalSections {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite (pullback.fst a b ≫ a)))]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (globalSections : CoefficientGlobalSections S)
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    DerivedCategory (ModuleCat.{u} (Scheme.globalSectionsRing S)) :=
  globalSections.obj
    ((RingedSite.Hom.modulePushforwardDerived (fiberCoefficientHom a b)).obj
      (externalTotal a b T hT F G))

/-- A tensor-compatible adjunction model for a chosen realization of derived global sections.
The coefficient-side derived tensor remains explicit because localization models need not be
definitionally equal. -/
abbrev CoefficientGlobalTensorModel (S : Scheme.{u})
    (globalSections : CoefficientGlobalSections S)
    (coefficientDerivedTensor :
      CoefficientDerived (𝟙 S) ⥤ CoefficientDerived (𝟙 S) ⥤ CoefficientDerived (𝟙 S)) :=
  CategoryTheory.Adjunction.TensorModel globalSections
    (AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor.globalSectionsCurried S.toRingedSpace)
    coefficientDerivedTensor

/-- The composite of a tensor comparison for derived global sections with derived global
sections of a supplied relative cup-product morphism. -/
noncomputable def globalCupProduct {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
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
          (externalTotal a b T hT F G)) :
    ((AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor.globalSectionsCurried
        S.toRingedSpace).obj (derivedGlobalSections a globalSections F)).obj
        (derivedGlobalSections b globalSections G) ⟶
      totalDerivedGlobalSections a b T hT globalSections F G :=
  model.cupProduct
      ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom a)).obj
        (coefficientObject a F))
      ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom b)).obj
        (coefficientObject b G)) ≫
    globalSections.map relativeCupProduct

/-- The generic global cup product is the tensor comparison followed by the image of the
supplied relative cup-product morphism. -/
theorem globalCupProduct_eq {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
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
          (externalTotal a b T hT F G)) :
    globalCupProduct a b T hT F G globalSections coefficientDerivedTensor model
        relativeCupProduct =
      model.cupProduct
          ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom a)).obj
            (coefficientObject a F))
          ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom b)).obj
            (coefficientObject b G)) ≫
        globalSections.map relativeCupProduct := sorry

section Canonical

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
variable
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

/-- The canonical global cup product from the derived tensor of the two derived global-section
objects to the derived global sections of their total external product. -/
noncomputable def canonicalGlobalCupProduct
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
      (RelativeCupProduct.coefficientDerivedTensor (𝟙 S))) :
    ((AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor.globalSectionsCurried
        S.toRingedSpace).obj (derivedGlobalSections a globalSections F)).obj
        (derivedGlobalSections b globalSections G) ⟶
      totalDerivedGlobalSections a b T hT globalSections F G :=
  globalCupProduct a b T hT F G globalSections
    (RelativeCupProduct.coefficientDerivedTensor (𝟙 S)) model
    (RelativeCupProduct.map a b T hT F G)

/-- The canonical global cup product is the tensor comparison followed by derived global
sections of the canonical relative cup-product map. -/
theorem canonicalGlobalCupProduct_eq
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
      (RelativeCupProduct.coefficientDerivedTensor (𝟙 S))) :
    canonicalGlobalCupProduct a b T hT F G globalSections model =
      model.cupProduct
          ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom a)).obj
            (coefficientObject a F))
          ((RingedSite.Hom.modulePushforwardDerived (coefficientPushforwardHom b)).obj
            (coefficientObject b G)) ≫
        globalSections.map (RelativeCupProduct.map a b T hT F G) := sorry

end Canonical

end AlgebraicGeometry.Scheme.Modules.Kunneth

end
