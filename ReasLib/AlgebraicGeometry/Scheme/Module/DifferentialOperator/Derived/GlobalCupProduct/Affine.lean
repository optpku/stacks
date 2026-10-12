/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.GlobalCupProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth

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
  [baseBifunctorHas : @CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
    (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
    _ _ _ _ _ _ _]
  [fiberBifunctorHas : @CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
    (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
  [baseLocalization :
    (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).IsLocalization
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (𝟙 S)))]
  [baseTensorLocalization :
    ((RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).prod
      (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))).IsLocalization
        (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.qis
          (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _)]
  [pullbackTensorTargetIsLeftDerived :
    RelativeCupProduct.PullbackTensorTargetIsLeftDerived a b]

/-- Over an affine base, the canonical global cup product of a bounded complex and a
bounded-below complex of relatively flat terms is an isomorphism when both source schemes
are compact with affine diagonal. -/
theorem canonicalGlobalCupProductIsIso
    [IsAffine S] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)]
    (globalSections : CoefficientGlobalSections S) [globalSections.IsEquivalence]
    (model : CoefficientGlobalTensorModel S globalSections
      (RelativeCupProduct.coefficientDerivedTensor (𝟙 S)))
    [Fact (CochainComplex.bounded _ F)] [Fact (CochainComplex.plus _ G)]
    [∀ n, SheafOfModules.IsFlatOver
      (Hom.FiniteOrderDifferentialOperatorCat.underlying a (F.X n)) a.toShHom]
    [∀ n, SheafOfModules.IsFlatOver
      (Hom.FiniteOrderDifferentialOperatorCat.underlying b (G.X n)) b.toShHom] :
    IsIso (@canonicalGlobalCupProduct S X Y a b
      _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _
      _ _ pullbackMonoidal baseTensorDescends fiberTensorDescends
      baseBifunctorHas fiberBifunctorHas pullbackTensorTargetIsLeftDerived
      T hT _ _ F G _ globalSections model) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth

end
