module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.GlobalCupProduct.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ComplexShape
open CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor
open RingedSite.Hom.DerivedAdjunction
open RingedSite.Hom.modulePullbackDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme
namespace Modules.Kunneth

/- Lemma 36.24.1: over an affine base, the canonical global cup product is an
isomorphism when the source schemes are quasi-compact with affine diagonal, `F` is bounded,
`G` is bounded below, and every term of both complexes is flat over the base. -/
@[stacks 0FLT] #check
  (AlgebraicGeometry.Scheme.Modules.Kunneth.canonicalGlobalCupProductIsIso :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [leftPushforwardIsRightAdjoint :
      (leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [rightPushforwardIsRightAdjoint :
      (rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [aPushforwardIsRightAdjoint :
      (coefficientPushforwardHom a).modulePushforward.IsRightAdjoint]
    [bPushforwardIsRightAdjoint :
      (coefficientPushforwardHom b).modulePushforward.IsRightAdjoint]
    [fiberPushforwardIsRightAdjoint :
      (fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [rightFiberPushforwardIsRightAdjoint :
      (rightFiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [leftPullbackHasLeftDerived : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite a))]
    [rightPullbackHasLeftDerived : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite b))]
    [aPullbackHasLeftDerived : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [bPullbackHasLeftDerived : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (coefficientPushforwardHom b))
      (RingedSite.Hom.ModuleQis
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [fiberPullbackHasLeftDerived : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [rightFiberPullbackHasLeftDerived : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (rightFiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [leftPushforwardHasRightDerived : Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite (pullback.fst a b ≫ a)))]
    [rightPushforwardHasRightDerived : Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite (pullback.fst a b ≫ a)))]
    [aPushforwardHasRightDerived : Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis (coefficientSite a))]
    [bPushforwardHasRightDerived : Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (coefficientPushforwardHom b))
      (RingedSite.Hom.ModuleQis (coefficientSite b))]
    [fiberPushforwardHasRightDerived : Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite (pullback.fst a b ≫ a)))]
    [rightFiberPushforwardHasRightDerived : Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived (rightFiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis (coefficientSite (pullback.fst a b ≫ a)))]
    [leftDerivedAdjunctionPair : HasPair (leftCoefficientHom a b)]
    [rightDerivedAdjunctionPair : HasPair (rightCoefficientHom a b)]
    [aDerivedAdjunctionPair : HasPair (coefficientPushforwardHom a)]
    [bDerivedAdjunctionPair : HasPair (coefficientPushforwardHom b)]
    [fiberDerivedAdjunctionPair : HasPair (fiberCoefficientHom a b)]
    [rightFiberDerivedAdjunctionPair : HasPair (rightFiberCoefficientHom a b)]
    [leftCompComparisonIsIso : IsIso (compComparison
      (leftCoefficientHom a b) (coefficientPushforwardHom a))]
    [rightCompComparisonIsIso : IsIso (compComparison
      (rightCoefficientHom a b) (coefficientPushforwardHom b))]
    [∀ K L : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))), GradedObject.HasTensor K L]
    [∀ K L M : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))),
      GradedObject.HasGoodTensor₁₂Tensor K L M]
    [∀ K L M : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))),
      GradedObject.HasGoodTensorTensor₂₃ K L M]
    [∀ K L M N : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))),
      GradedObject.HasTensor₄ObjExt K L M N]
    [∀ K L : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))),
      GradedObject.HasTensor K L]
    [∀ K L M : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))),
      GradedObject.HasGoodTensor₁₂Tensor K L M]
    [∀ K L M : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))),
      GradedObject.HasGoodTensorTensor₂₃ K L M]
    [∀ K L M N : GradedObject ℤ
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))),
      GradedObject.HasTensor₄ObjExt K L M N]
    [baseTensorDescends : @HomotopyCategory.Koszul.TensorDescends
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _ _ _ _ _ _ _ _]
    [fiberTensorDescends : @HomotopyCategory.Koszul.TensorDescends
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a)))
      _ _ _ _ _ _ _ _ _]
    [pullbackMonoidal : @Functor.Monoidal _ _
      (@HomotopyCategory.Koszul.monoidalCategory
        (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S)))
        _ _ _ _ _ _ _ _ _ _ _) _ _
      (@HomotopyCategory.Koszul.monoidalCategory
        (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a)))
        _ _ _ _ _ _ _ _ _ _ _)
      (RingedSite.Hom.modulePullbackHomotopy.{u} (fiberCoefficientHom a b))]
    [baseBifunctorHas : @Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _ _ _ _ _ _ _ _ _]
    [fiberBifunctorHas : @Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a)))
      _ _ _ _ _ _ _ _ _ _]
    [baseLocalization :
      (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).IsLocalization
        (RingedSite.Hom.ModuleQis.{u} (coefficientSite (𝟙 S)))]
    [baseTensorLocalization :
      ((RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).prod
        (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))).IsLocalization
          (@Bifunctor.qis
            (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _)]
    [pullbackTensorTargetIsLeftDerived :
      RelativeCupProduct.PullbackTensorTargetIsLeftDerived a b]
    [IsAffine S] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [TPreservesZeroMorphisms : T.PreservesZeroMorphisms]
    [TObjPreservesZeroMorphisms : ∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [hasMapBifunctor : HomologicalComplex.HasMapBifunctor F G T (up ℤ)]
    (globalSections : CoefficientGlobalSections S)
    [globalSections.IsEquivalence]
    (model : CoefficientGlobalTensorModel S globalSections
      (RelativeCupProduct.coefficientDerivedTensor (𝟙 S)))
    [Fact (CochainComplex.bounded _ F)] [Fact (CochainComplex.plus _ G)]
    [∀ n, SheafOfModules.IsFlatOver
      (Hom.FiniteOrderDifferentialOperatorCat.underlying a (F.X n)) a.toShHom]
    [∀ n, SheafOfModules.IsFlatOver
      (Hom.FiniteOrderDifferentialOperatorCat.underlying b (G.X n)) b.toShHom],
    IsIso (@canonicalGlobalCupProduct S X Y a b
      leftPushforwardIsRightAdjoint rightPushforwardIsRightAdjoint
      aPushforwardIsRightAdjoint bPushforwardIsRightAdjoint
      fiberPushforwardIsRightAdjoint rightFiberPushforwardIsRightAdjoint
      leftPullbackHasLeftDerived rightPullbackHasLeftDerived
      aPullbackHasLeftDerived bPullbackHasLeftDerived
      fiberPullbackHasLeftDerived rightFiberPullbackHasLeftDerived
      leftPushforwardHasRightDerived rightPushforwardHasRightDerived
      aPushforwardHasRightDerived bPushforwardHasRightDerived
      fiberPushforwardHasRightDerived rightFiberPushforwardHasRightDerived
      leftDerivedAdjunctionPair rightDerivedAdjunctionPair
      aDerivedAdjunctionPair bDerivedAdjunctionPair
      fiberDerivedAdjunctionPair rightFiberDerivedAdjunctionPair
      leftCompComparisonIsIso rightCompComparisonIsIso pullbackMonoidal
      baseTensorDescends fiberTensorDescends baseBifunctorHas fiberBifunctorHas
      pullbackTensorTargetIsLeftDerived T hT TPreservesZeroMorphisms
      TObjPreservesZeroMorphisms F G hasMapBifunctor globalSections model))

end Modules.Kunneth
end AlgebraicGeometry.Scheme

end
