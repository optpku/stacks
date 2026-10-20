/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Derived

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

variable {S X Y : Scheme.{u}}

/-- The coefficient realization of the extended operator de Rham complex, localized to the
derived category, is canonically isomorphic to the standard relative de Rham complex. -/
noncomputable def operatorDerivedDeRhamIso (a : X ⟶ S) :
    Modules.Kunneth.coefficientObject a (extendedOperatorComplex a) ≅
      Scheme.DeRham.DerivedPushforward.derivedComplex a :=
  (RingedSite.Hom.moduleLocalization
    (Modules.Kunneth.coefficientSite a)).mapIso
      ((HomotopyCategory.quotient _ (up ℤ)).mapIso (operatorDeRhamIso a))

/-- The forward map of `operatorDerivedDeRhamIso` is the localization of the standard
operator-complex comparison. -/
theorem operatorDerivedDeRhamIso_hom (a : X ⟶ S) :
    (operatorDerivedDeRhamIso a).hom =
      (RingedSite.Hom.moduleLocalization
        (Modules.Kunneth.coefficientSite a)).map
          ((HomotopyCategory.quotient _ (up ℤ)).map (operatorDeRhamIso a).hom) := sorry

variable (a : X ⟶ S) (b : Y ⟶ S)
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

/-- The canonical relative de Rham cup-product comparison over an arbitrary base scheme. -/
noncomputable def relativeComparison :
    ((Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S)).obj
      ((RingedSite.Hom.modulePushforwardDerived
        (Modules.Kunneth.coefficientPushforwardHom a)).obj
          (Scheme.DeRham.DerivedPushforward.derivedComplex a))).obj
      ((RingedSite.Hom.modulePushforwardDerived
        (Modules.Kunneth.coefficientPushforwardHom b)).obj
          (Scheme.DeRham.DerivedPushforward.derivedComplex b)) ⟶
    (RingedSite.Hom.modulePushforwardDerived
      (Modules.Kunneth.fiberCoefficientHom a b)).obj
        (Scheme.DeRham.DerivedPushforward.derivedComplex (pullback.fst a b ≫ a)) :=
  ((Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S)).map
      ((RingedSite.Hom.modulePushforwardDerived
        (Modules.Kunneth.coefficientPushforwardHom a)).map
          (operatorDerivedDeRhamIso a).inv)).app _ ≫
    ((Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S)).obj _).map
      ((RingedSite.Hom.modulePushforwardDerived
        (Modules.Kunneth.coefficientPushforwardHom b)).map
          (operatorDerivedDeRhamIso b).inv) ≫
    @Scheme.RelativeCupProduct.map S X Y a b
      _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _
      _ _ pullbackMonoidal baseTensorDescends fiberTensorDescends
      baseBifunctorHas fiberBifunctorHas pullbackTensorTargetIsLeftDerived
      T hT _ _ (extendedOperatorComplex a) (extendedOperatorComplex b) _ ≫
    (RingedSite.Hom.modulePushforwardDerived
      (Modules.Kunneth.fiberCoefficientHom a b)).map (derivedComparison a b T hT)

/-- The relative comparison factors through the operator-complex relative cup product and
the localized external de Rham comparison. -/
theorem relativeComparison_eq :
    relativeComparison a b T hT =
      ((Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S)).map
        ((RingedSite.Hom.modulePushforwardDerived
          (Modules.Kunneth.coefficientPushforwardHom a)).map
            (operatorDerivedDeRhamIso a).inv)).app _ ≫
      ((Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 S)).obj _).map
        ((RingedSite.Hom.modulePushforwardDerived
          (Modules.Kunneth.coefficientPushforwardHom b)).map
            (operatorDerivedDeRhamIso b).inv) ≫
      @Scheme.RelativeCupProduct.map S X Y a b
        _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _
        _ _ pullbackMonoidal baseTensorDescends fiberTensorDescends
        baseBifunctorHas fiberBifunctorHas pullbackTensorTargetIsLeftDerived
        T hT _ _ (extendedOperatorComplex a) (extendedOperatorComplex b) _ ≫
      (RingedSite.Hom.modulePushforwardDerived
        (Modules.Kunneth.fiberCoefficientHom a b)).map
          (derivedComparison a b T hT) := sorry


/-- For smooth quasi-compact morphisms with affine relative diagonals, the relative de Rham
cup-product comparison is an isomorphism. -/
instance relativeComparison_isIso
    [Smooth a] [Smooth b] [QuasiCompact a] [QuasiCompact b]
    [IsAffineHom (pullback.diagonal a)] [IsAffineHom (pullback.diagonal b)] :
    IsIso (relativeComparison a b T hT) := sorry

end AlgebraicGeometry.Scheme.DeRham.Kunneth
