/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.GlobalCupProduct.Affine
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
variable (T : FiniteOrderDifferentialOperatorCat a ⥤
  FiniteOrderDifferentialOperatorCat b ⥤
    FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
variable (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
variable [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
variable [HomologicalComplex.HasMapBifunctor
  (operatorComplex a) (operatorComplex b) T (up ℕ)]
variable [HomologicalComplex.HasMapBifunctor
  (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)]

/-- The de Rham comparison localized from complexes to the coefficient derived category. -/
noncomputable def derivedComparison :
    Modules.Kunneth.externalTotal a b T hT
        (extendedOperatorComplex a) (extendedOperatorComplex b) ⟶
      Scheme.DeRham.DerivedPushforward.derivedComplex (pullback.fst a b ≫ a) :=
  (RingedSite.Hom.moduleLocalization
    (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))).map
      ((HomotopyCategory.quotient _ (up ℤ)).map (comparison a b T hT))

/-- The localized de Rham comparison is the image of the chain-level comparison. -/
theorem derivedComparison_eq :
    derivedComparison a b T hT =
      (RingedSite.Hom.moduleLocalization
        (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))).map
          ((HomotopyCategory.quotient _ (up ℤ)).map (comparison a b T hT)) := sorry

/-- The localized de Rham comparison is an isomorphism. -/
theorem derivedComparison_isIso : IsIso (derivedComparison a b T hT) := sorry

section Global

variable
  [(Modules.Kunneth.leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.coefficientPushforwardHom a).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.coefficientPushforwardHom b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.rightFiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.leftCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite a))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.rightCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite b))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom a))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.fiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.rightFiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.leftCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.rightCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom a))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite a))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite b))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.fiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.rightFiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.leftCoefficientHom a b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.rightCoefficientHom a b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.coefficientPushforwardHom a)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.coefficientPushforwardHom b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.fiberCoefficientHom a b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.rightFiberCoefficientHom a b)]
  [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
    (Modules.Kunneth.leftCoefficientHom a b) (Modules.Kunneth.coefficientPushforwardHom a))]
  [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
    (Modules.Kunneth.rightCoefficientHom a b) (Modules.Kunneth.coefficientPushforwardHom b))]
  [∀ K L : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S))),
    GradedObject.HasTensor K L]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S))),
    GradedObject.HasGoodTensor₁₂Tensor K L M]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S))),
    GradedObject.HasGoodTensorTensor₂₃ K L M]
  [∀ K L M N : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S))),
    GradedObject.HasTensor₄ObjExt K L M N]
  [∀ K L : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasTensor K L]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasGoodTensor₁₂Tensor K L M]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasGoodTensorTensor₂₃ K L M]
  [∀ K L M N : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasTensor₄ObjExt K L M N]
  [baseTensorDescends : @HomotopyCategory.Koszul.TensorDescends
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S)))
    _ _ _ _ _ _ _ _ _]
  [fiberTensorDescends : @HomotopyCategory.Koszul.TensorDescends
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))
    _ _ _ _ _ _ _ _ _]
  [pullbackMonoidal : @Functor.Monoidal _ _
    (@HomotopyCategory.Koszul.monoidalCategory
      (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _ _ _ _ _) _ _
    (@HomotopyCategory.Koszul.monoidalCategory
      (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))
      _ _ _ _ _ _ _ _ _ _ _)
    (RingedSite.Hom.modulePullbackHomotopy.{u} (Modules.Kunneth.fiberCoefficientHom a b))]
  [baseBifunctorHas : @DerivedCategory.DerivedTensor.Bifunctor.Has
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory (Modules.Kunneth.coefficientSite (𝟙 S)))
    _ _ _ _ _ _ _]
  [fiberBifunctorHas : @DerivedCategory.DerivedTensor.Bifunctor.Has
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
  [baseLocalization :
    (RingedSite.Hom.moduleLocalization.{u}
      (Modules.Kunneth.coefficientSite (𝟙 S))).IsLocalization
        (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (𝟙 S)))]
  [baseTensorLocalization :
    ((RingedSite.Hom.moduleLocalization.{u}
      (Modules.Kunneth.coefficientSite (𝟙 S))).prod
        (RingedSite.Hom.moduleLocalization.{u}
          (Modules.Kunneth.coefficientSite (𝟙 S)))).IsLocalization
      (@DerivedCategory.DerivedTensor.Bifunctor.qis
        (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 S))) _ _)]
  [pullbackTensorTargetIsLeftDerived :
    Scheme.RelativeCupProduct.PullbackTensorTargetIsLeftDerived a b]

/-- The global de Rham Künneth morphism: the canonical global cup product followed by the
localized comparison with the de Rham complex of the fiber product. -/
noncomputable def globalComparison
    (globalSections : Modules.Kunneth.CoefficientGlobalSections S)
    (model : Modules.Kunneth.CoefficientGlobalTensorModel S globalSections
      (Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S))) :
    ((RingedSpace.ModuleDerived.Tensor.globalSectionsCurried S.toRingedSpace).obj
        (Modules.Kunneth.derivedGlobalSections a globalSections (extendedOperatorComplex a))).obj
        (Modules.Kunneth.derivedGlobalSections b globalSections (extendedOperatorComplex b)) ⟶
      globalSections.obj
        ((RingedSite.Hom.modulePushforwardDerived
          (Modules.Kunneth.fiberCoefficientHom a b)).obj
            (Scheme.DeRham.DerivedPushforward.derivedComplex (pullback.fst a b ≫ a))) :=
  @Modules.Kunneth.canonicalGlobalCupProduct S X Y a b
      _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _
      _ _ pullbackMonoidal baseTensorDescends fiberTensorDescends
      baseBifunctorHas fiberBifunctorHas pullbackTensorTargetIsLeftDerived
      T hT _ _ (extendedOperatorComplex a) (extendedOperatorComplex b) _
      globalSections model ≫
    globalSections.map
      ((RingedSite.Hom.modulePushforwardDerived
        (Modules.Kunneth.fiberCoefficientHom a b)).map (derivedComparison a b T hT))

/-- The global comparison is the canonical global cup product followed by derived global
sections of the localized de Rham comparison. -/
theorem globalComparison_eq
    (globalSections : Modules.Kunneth.CoefficientGlobalSections S)
    (model : Modules.Kunneth.CoefficientGlobalTensorModel S globalSections
      (Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S))) :
    globalComparison a b T hT globalSections model =
      @Modules.Kunneth.canonicalGlobalCupProduct S X Y a b
          _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _
          _ _ pullbackMonoidal baseTensorDescends fiberTensorDescends
          baseBifunctorHas fiberBifunctorHas pullbackTensorTargetIsLeftDerived
          T hT _ _ (extendedOperatorComplex a) (extendedOperatorComplex b) _
          globalSections model ≫
        globalSections.map
          ((RingedSite.Hom.modulePushforwardDerived
            (Modules.Kunneth.fiberCoefficientHom a b)).map
              (derivedComparison a b T hT)) := sorry

end Global

end AlgebraicGeometry.Scheme.DeRham.Kunneth

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

variable {A : CommRingCat.{u}} {X Y : Scheme.{u}}
variable (a : X ⟶ Spec A) (b : Y ⟶ Spec A)
variable (T : FiniteOrderDifferentialOperatorCat a ⥤
  FiniteOrderDifferentialOperatorCat b ⥤
    FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
variable (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
variable [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
variable [HomologicalComplex.HasMapBifunctor
  (operatorComplex a) (operatorComplex b) T (up ℕ)]
variable [HomologicalComplex.HasMapBifunctor
  (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)]
variable
  [(Modules.Kunneth.leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.coefficientPushforwardHom a).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.coefficientPushforwardHom b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.rightFiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.leftCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite a))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.rightCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite b))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom a))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.fiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.rightFiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.leftCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.rightCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom a))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite a))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite b))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.fiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.rightFiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.leftCoefficientHom a b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.rightCoefficientHom a b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.coefficientPushforwardHom a)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.coefficientPushforwardHom b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.fiberCoefficientHom a b)]
  [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (Modules.Kunneth.rightFiberCoefficientHom a b)]
  [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
    (Modules.Kunneth.leftCoefficientHom a b) (Modules.Kunneth.coefficientPushforwardHom a))]
  [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
    (Modules.Kunneth.rightCoefficientHom a b) (Modules.Kunneth.coefficientPushforwardHom b))]
  [∀ K L : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasTensor K L]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasGoodTensor₁₂Tensor K L M]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasGoodTensorTensor₂₃ K L M]
  [∀ K L M N : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasTensor₄ObjExt K L M N]
  [∀ K L : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasTensor K L]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasGoodTensor₁₂Tensor K L M]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasGoodTensorTensor₂₃ K L M]
  [∀ K L M N : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasTensor₄ObjExt K L M N]
  [baseTensorDescends : @HomotopyCategory.Koszul.TensorDescends
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))
    _ _ _ _ _ _ _ _ _]
  [fiberTensorDescends : @HomotopyCategory.Koszul.TensorDescends
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))
    _ _ _ _ _ _ _ _ _]
  [pullbackMonoidal : @Functor.Monoidal _ _
    (@HomotopyCategory.Koszul.monoidalCategory
      (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))
      _ _ _ _ _ _ _ _ _ _ _) _ _
    (@HomotopyCategory.Koszul.monoidalCategory
      (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))
      _ _ _ _ _ _ _ _ _ _ _)
    (RingedSite.Hom.modulePullbackHomotopy.{u} (Modules.Kunneth.fiberCoefficientHom a b))]
  [baseBifunctorHas : @DerivedCategory.DerivedTensor.Bifunctor.Has
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))) _ _ _ _ _ _ _]
  [fiberBifunctorHas : @DerivedCategory.DerivedTensor.Bifunctor.Has
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
  [baseLocalization :
    (RingedSite.Hom.moduleLocalization.{u}
      (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))).IsLocalization
        (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))]
  [baseTensorLocalization :
    ((RingedSite.Hom.moduleLocalization.{u}
      (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))).prod
        (RingedSite.Hom.moduleLocalization.{u}
          (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))).IsLocalization
      (@DerivedCategory.DerivedTensor.Bifunctor.qis
        (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))) _ _)]
  [pullbackTensorTargetIsLeftDerived :
    Scheme.RelativeCupProduct.PullbackTensorTargetIsLeftDerived a b]

/-- The de Rham Künneth morphism over `Spec A`, transported from modules over global
sections to an actual morphism in `D(A)`. -/
noncomputable def affineComparison
    (globalSections : Modules.Kunneth.CoefficientGlobalSections (Spec A))
    (model : Modules.Kunneth.CoefficientGlobalTensorModel (Spec A) globalSections
      (Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 (Spec A)))) :
    (ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (((RingedSpace.ModuleDerived.Tensor.globalSectionsCurried
        (Spec A).toRingedSpace).obj
          (Modules.Kunneth.derivedGlobalSections a globalSections
            (extendedOperatorComplex a))).obj
          (Modules.Kunneth.derivedGlobalSections b globalSections
            (extendedOperatorComplex b))) ⟶
      (ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom).obj
        (globalSections.obj
          ((RingedSite.Hom.modulePushforwardDerived
            (Modules.Kunneth.fiberCoefficientHom a b)).obj
              (Scheme.DeRham.DerivedPushforward.derivedComplex (pullback.fst a b ≫ a)))) :=
  (ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom).map
    (globalComparison a b T hT globalSections model)

/-- The affine comparison is restriction of scalars of the intrinsic global comparison. -/
theorem affineComparison_eq
    (globalSections : Modules.Kunneth.CoefficientGlobalSections (Spec A))
    (model : Modules.Kunneth.CoefficientGlobalTensorModel (Spec A) globalSections
      (Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 (Spec A)))) :
    affineComparison a b T hT globalSections model =
      (ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom).map
        (globalComparison a b T hT globalSections model) := sorry

open DerivedCategory.DerivedTensor RingedSite.Hom

variable {A : CommRingCat.{u}} {X Y : Scheme.{u}}
variable (a : X ⟶ Spec A) (b : Y ⟶ Spec A)
variable (T : FiniteOrderDifferentialOperatorCat a ⥤
  FiniteOrderDifferentialOperatorCat b ⥤
    FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
variable (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
variable [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
variable [HomologicalComplex.HasMapBifunctor
  (operatorComplex a) (operatorComplex b) T (up ℕ)]
variable [HomologicalComplex.HasMapBifunctor
  (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)]
variable
  [(Modules.Kunneth.leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.coefficientPushforwardHom a).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.coefficientPushforwardHom b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [(Modules.Kunneth.rightFiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.leftCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite a))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.rightCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite b))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom a))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.fiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{u} (Modules.Kunneth.rightFiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (𝟙 (Spec A).toRingedSpace)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.leftCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.rightCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom a))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite a))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.coefficientPushforwardHom b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite b))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.fiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [Functor.HasRightDerivedFunctor
    (RingedSite.Hom.modulePushforwardToDerived.{u} (Modules.Kunneth.rightFiberCoefficientHom a b))
    (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))]
  [DerivedAdjunction.HasPair.{u} (Modules.Kunneth.leftCoefficientHom a b)]
  [DerivedAdjunction.HasPair.{u} (Modules.Kunneth.rightCoefficientHom a b)]
  [DerivedAdjunction.HasPair.{u} (Modules.Kunneth.coefficientPushforwardHom a)]
  [DerivedAdjunction.HasPair.{u} (Modules.Kunneth.coefficientPushforwardHom b)]
  [DerivedAdjunction.HasPair.{u} (Modules.Kunneth.fiberCoefficientHom a b)]
  [DerivedAdjunction.HasPair.{u} (Modules.Kunneth.rightFiberCoefficientHom a b)]
  [IsIso (modulePullbackDerived.compComparison
    (Modules.Kunneth.leftCoefficientHom a b) (Modules.Kunneth.coefficientPushforwardHom a))]
  [IsIso (modulePullbackDerived.compComparison
    (Modules.Kunneth.rightCoefficientHom a b) (Modules.Kunneth.coefficientPushforwardHom b))]
  [∀ K L : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasTensor K L]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasGoodTensor₁₂Tensor K L M]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasGoodTensorTensor₂₃ K L M]
  [∀ K L M N : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))),
    GradedObject.HasTensor₄ObjExt K L M N]
  [∀ K L : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasTensor K L]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasGoodTensor₁₂Tensor K L M]
  [∀ K L M : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasGoodTensorTensor₂₃ K L M]
  [∀ K L M N : GradedObject ℤ
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))),
    GradedObject.HasTensor₄ObjExt K L M N]
  [baseTensorDescends : @HomotopyCategory.Koszul.TensorDescends
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))
    _ _ _ _ _ _ _ _ _]
  [fiberTensorDescends : @HomotopyCategory.Koszul.TensorDescends
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))
    _ _ _ _ _ _ _ _ _]
  [pullbackMonoidal : @Functor.Monoidal _ _
    (@HomotopyCategory.Koszul.monoidalCategory
      (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))
      _ _ _ _ _ _ _ _ _ _ _) _ _
    (@HomotopyCategory.Koszul.monoidalCategory
      (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a)))
      _ _ _ _ _ _ _ _ _ _ _)
    (RingedSite.Hom.modulePullbackHomotopy.{u} (Modules.Kunneth.fiberCoefficientHom a b))]
  [baseBifunctorHas : @Bifunctor.Has
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))) _ _ _ _ _ _ _]
  [fiberBifunctorHas : @Bifunctor.Has
    (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (Modules.Kunneth.coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
  [baseLocalization :
    (RingedSite.Hom.moduleLocalization.{u}
      (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))).IsLocalization
        (RingedSite.Hom.ModuleQis.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))]
  [baseTensorLocalization :
    ((RingedSite.Hom.moduleLocalization.{u}
      (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))).prod
        (RingedSite.Hom.moduleLocalization.{u}
          (Modules.Kunneth.coefficientSite (𝟙 (Spec A))))).IsLocalization
      (@Bifunctor.qis
        (RingedSite.ModuleCat.{u} (Modules.Kunneth.coefficientSite (𝟙 (Spec A)))) _ _)]
  [pullbackTensorTargetIsLeftDerived :
    Scheme.RelativeCupProduct.PullbackTensorTargetIsLeftDerived a b]


/-- The affine de Rham Künneth comparison is an isomorphism for smooth quasi-compact
schemes with affine diagonal over an affine base. -/
theorem affineComparison_isIso
    [Smooth a] [Smooth b] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
    (globalSections : Modules.Kunneth.CoefficientGlobalSections (Spec A))
    [globalSections.IsEquivalence]
    (model : Modules.Kunneth.CoefficientGlobalTensorModel (Spec A) globalSections
      (Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 (Spec A)))) :
    IsIso (affineComparison a b T hT globalSections model) := sorry

end AlgebraicGeometry.Scheme.DeRham.Kunneth

