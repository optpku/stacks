/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Derived
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.Scheme.Hom
open DerivedCategory.DerivedTensor RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham
namespace Kunneth

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
  [(RingedSite.Hom.modulePushforward.{u} (Modules.Kunneth.leftCoefficientHom a b)).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u} (Modules.Kunneth.rightCoefficientHom a b)).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u} (Modules.Kunneth.coefficientPushforwardHom a)).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u} (Modules.Kunneth.coefficientPushforwardHom b)).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u} (Modules.Kunneth.fiberCoefficientHom a b)).IsRightAdjoint]
  [(RingedSite.Hom.modulePushforward.{u} (Modules.Kunneth.rightFiberCoefficientHom a b)).IsRightAdjoint]
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

variable [Smooth a] [Smooth b] [CompactSpace X] [CompactSpace Y]
variable [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
variable [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
variable (globalSections : Modules.Kunneth.CoefficientGlobalSections (Spec A))
variable [globalSections.IsEquivalence]
variable (model : Modules.Kunneth.CoefficientGlobalTensorModel (Spec A) globalSections
  (Scheme.RelativeCupProduct.coefficientDerivedTensor (𝟙 (Spec A))))

/- Lemma 50.8.2: for smooth quasi-compact schemes with affine diagonal over Spec A, the
canonical map from the derived tensor of their derived de Rham global sections to the derived
de Rham global sections of their fiber product is an isomorphism in D(A). -/
@[stacks 0FMB] #check
  (AlgebraicGeometry.Scheme.DeRham.Kunneth.affineComparison_isIso
    (a := a) (b := b) (T := T) (hT := hT) globalSections model :
    IsIso (AlgebraicGeometry.Scheme.DeRham.Kunneth.affineComparison
      a b T hT globalSections model))

end Kunneth
end AlgebraicGeometry.Scheme.DeRham
