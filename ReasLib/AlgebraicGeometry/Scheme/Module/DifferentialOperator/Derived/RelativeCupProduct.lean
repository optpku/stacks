/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition.Canonical
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Monoidal
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.Functor.Derived.TensorComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.ExternalProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeCupProduct

open Modules.Kunneth

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The canonical curried derived tensor on coefficient-derived modules. -/
noncomputable abbrev coefficientDerivedTensor {Z W : Scheme.{u}} (f : Z ⟶ W)
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
      _ _ _ _ _ _ _] :
    CoefficientDerived f ⥤ CoefficientDerived f ⥤ CoefficientDerived f :=
  Functor.curry.obj
    (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
      (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
      _ _ _ _ _ _ _ _)

/-- `coefficientDerivedTensor` is the curried canonical two-variable derived tensor. -/
theorem coefficientDerivedTensor_def {Z W : Scheme.{u}} (f : Z ⟶ W)
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
      _ _ _ _ _ _ _] :
    coefficientDerivedTensor f = Functor.curry.obj
      (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
        (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
        _ _ _ _ _ _ _ _) := sorry

/-- The canonical derived-tensor counit in the tensor-then-localize presentation. -/
noncomputable abbrev coefficientTensorCounit {Z W : Scheme.{u}} (f : Z ⟶ W)
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u} (coefficientSite f))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
      _ _ _ _ _ _ _] :
    (RingedSite.Hom.moduleLocalization.{u} (coefficientSite f)).prod
          (RingedSite.Hom.moduleLocalization.{u} (coefficientSite f)) ⋙
        (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
          (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
          (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
          _ _ _ _ _ _ _ _) ⟶
      MonoidalCategory.tensor
          (RingedSite.Hom.ModuleHomotopy.{u} (coefficientSite f)) ⋙
        RingedSite.Hom.moduleLocalization.{u} (coefficientSite f) :=
  (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.counit
      (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
      _ _ _ _ _ _ _ _) ≫
    (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorIso
      (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
      _ _ _ _ _ _ _).inv

/-- The coefficient tensor counit is the universal biderived counit transported to the
ordinary total-complex presentation. -/
theorem coefficientTensorCounit_def {Z W : Scheme.{u}} (f : Z ⟶ W)
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u} (coefficientSite f))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
      _ _ _ _ _ _ _] :
    coefficientTensorCounit f =
      (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.counit
        (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
        _ _ _ _ _ _ _ _) ≫
        (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorIso
          (RingedSite.ModuleCat.{u} (coefficientSite f)) _ _
          (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite f))
          _ _ _ _ _ _ _).inv := sorry

/-- The universal-property condition selecting the canonical pullback/tensor comparison. -/
abbrev PullbackTensorTargetIsLeftDerived
    [(fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [hPullback : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u}
        (coefficientSite (pullback.fst a b ≫ a)))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S)))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _]
    [hBaseLocalization :
      (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).IsLocalization
        (RingedSite.Hom.ModuleQis.{u} (coefficientSite (𝟙 S)))]
    [hTensorLocalization :
      ((RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).prod
          (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))).IsLocalization
        (CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.qis
          (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))))] : Prop :=
  @Functor.IsLeftDerivedFunctor _ _ _ _ _ _
    ((RingedSite.Hom.modulePullbackDerived.{u} (fiberCoefficientHom a b)).prod
        (RingedSite.Hom.modulePullbackDerived.{u} (fiberCoefficientHom a b)) ⋙
      (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
        (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory
          (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _ _))
    _ _
    (CategoryTheory.Functor.LeftDerived.TensorComparison.targetCounit
      (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))
      (RingedSite.Hom.moduleLocalization.{u}
        (coefficientSite (pullback.fst a b ≫ a)))
      (RingedSite.Hom.modulePullbackHomotopy.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.modulePullbackDerived.{u} (fiberCoefficientHom a b))
      (MonoidalCategory.tensor (RingedSite.Hom.ModuleHomotopy.{u}
        (coefficientSite (pullback.fst a b ≫ a))))
      (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
        (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory
          (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _ _)
      (@Functor.totalLeftDerivedCounit _ _ _ _ _ _
        (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
        (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))
        (RingedSite.Hom.ModuleQis.{u} (coefficientSite (𝟙 S)))
        hBaseLocalization hPullback)
      (coefficientTensorCounit (pullback.fst a b ≫ a)))
    (CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.qis
      (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S)))) hTensorLocalization

/-- The canonical biderived comparison from pullback of a coefficient tensor to the tensor
of the two derived coefficient pullbacks. -/
noncomputable def pullbackTensorComparison
    [(fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [hPullback : Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.Monoidal
      (RingedSite.Hom.modulePullbackHomotopy.{u} (fiberCoefficientHom a b))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u}
        (coefficientSite (pullback.fst a b ≫ a)))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S)))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _]
    [hBaseLocalization :
      (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).IsLocalization
        (RingedSite.Hom.ModuleQis.{u} (coefficientSite (𝟙 S)))]
    [hLocalization :
      ((RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).prod
          (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))).IsLocalization
        (CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.qis
          (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))))]
    [hTarget : PullbackTensorTargetIsLeftDerived a b] :
    (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _ _) ⋙
        RingedSite.Hom.modulePullbackDerived.{u} (fiberCoefficientHom a b) ⟶
      (RingedSite.Hom.modulePullbackDerived.{u} (fiberCoefficientHom a b)).prod
          (RingedSite.Hom.modulePullbackDerived.{u} (fiberCoefficientHom a b)) ⋙
        (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
          (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
          (RingedSite.Hom.moduleCat_hasDerivedCategory
            (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _ _) :=
  @CategoryTheory.Functor.LeftDerived.TensorComparison.comparison _ _ _ _ _ _ _ _
    (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))
    (RingedSite.Hom.moduleLocalization.{u}
      (coefficientSite (pullback.fst a b ≫ a)))
    (RingedSite.Hom.modulePullbackHomotopy.{u} (fiberCoefficientHom a b))
    (RingedSite.Hom.modulePullbackDerived.{u} (fiberCoefficientHom a b))
    (MonoidalCategory.tensor
      (RingedSite.Hom.ModuleHomotopy.{u} (coefficientSite (𝟙 S))))
    (MonoidalCategory.tensor (RingedSite.Hom.ModuleHomotopy.{u}
      (coefficientSite (pullback.fst a b ≫ a))))
    (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _ _)
    (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _ _)
    (CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.qis
      (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))))
    hLocalization
    (@Functor.totalLeftDerivedCounit _ _ _ _ _ _
      (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S)))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (𝟙 S)))
      hBaseLocalization hPullback)
    (coefficientTensorCounit (𝟙 S))
    (coefficientTensorCounit (pullback.fst a b ≫ a))
    (Functor.Monoidal.μNatIso
      (RingedSite.Hom.modulePullbackHomotopy.{u} (fiberCoefficientHom a b))) hTarget

/-- The adjunction-unit and pushforward-composition map from `R(a)_*F` to the direct
image of the canonical coefficient pullback of `F` on `X ×_S Y`. -/
noncomputable def leftLeg
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(coefficientPushforwardHom a).modulePushforward.IsRightAdjoint]
    [(fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (coefficientPushforwardHom a))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (leftCoefficientHom a b)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (coefficientPushforwardHom a)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (fiberCoefficientHom a b)]
    [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
      (leftCoefficientHom a b) (coefficientPushforwardHom a))]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ) :
    (RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom a)).obj
        (coefficientObject a F) ⟶
      (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj
        ((RingedSite.Hom.modulePullbackDerived.{u} (leftCoefficientHom a b)).obj
          (coefficientObject a F)) :=
  (RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom a)).map
      ((RingedSite.Hom.moduleDerivedAdjunction.{u} (leftCoefficientHom a b)).unit.app
        (coefficientObject a F)) ≫
    (RingedSite.Hom.modulePushforwardDerived.compIso
      (leftCoefficientHom a b) (coefficientPushforwardHom a) inferInstance).hom.app _

/-- The two coefficient-site presentations of the derived direct image through the second
fiber-product projection agree on every object. -/
theorem rightFiberPushforward_obj_eq
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (rightFiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    (K : CoefficientDerived (pullback.fst a b ≫ a)) :
    (RingedSite.Hom.modulePushforwardDerived.{u} (rightFiberCoefficientHom a b)).obj K =
      (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj K := sorry

/-- The adjunction-unit and pushforward-composition map from `R(b)_*G` to the direct
image of the canonical coefficient pullback of `G` on `X ×_S Y`. -/
noncomputable def rightLeg
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(coefficientPushforwardHom b).modulePushforward.IsRightAdjoint]
    [(rightFiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (coefficientPushforwardHom b))
      (RingedSite.Hom.ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (rightFiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (coefficientPushforwardHom b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (rightFiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (rightCoefficientHom a b)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (coefficientPushforwardHom b)]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (rightFiberCoefficientHom a b)]
    [IsIso (RingedSite.Hom.modulePullbackDerived.compComparison
      (rightCoefficientHom a b) (coefficientPushforwardHom b))]
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) :
    (RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom b)).obj
        (coefficientObject b G) ⟶
      (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj
        ((RingedSite.Hom.modulePullbackDerived.{u} (rightCoefficientHom a b)).obj
          (coefficientObject b G)) :=
  (RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom b)).map
      ((RingedSite.Hom.moduleDerivedAdjunction.{u} (rightCoefficientHom a b)).unit.app
        (coefficientObject b G)) ≫
    (RingedSite.Hom.modulePushforwardDerived.compIso
      (rightCoefficientHom a b) (coefficientPushforwardHom b) inferInstance).hom.app _ ≫
    eqToHom (rightFiberPushforward_obj_eq a b
      ((RingedSite.Hom.modulePullbackDerived.{u} (rightCoefficientHom a b)).obj
        (coefficientObject b G)))

/-- The canonical relative cup product for coefficient-derived modules on the fiber product. -/
noncomputable def cupProduct
    [(fiberCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (𝟙 S.toRingedSpace)))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived.{u} (fiberCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (pullback.fst a b ≫ a)))]
    [RingedSite.Hom.DerivedAdjunction.HasPair.{u} (fiberCoefficientHom a b)]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
    [Functor.Monoidal
      (RingedSite.Hom.modulePullbackHomotopy.{u} (fiberCoefficientHom a b))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S)))]
    [HomotopyCategory.Koszul.TensorDescends
      (C := RingedSite.ModuleCat.{u}
        (coefficientSite (pullback.fst a b ≫ a)))]
    [(RingedSite.Hom.moduleLocalization.{u} (coefficientSite (𝟙 S))).IsLocalization
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite (𝟙 S)))]
    [PullbackTensorTargetIsLeftDerived a b]
    (K L : CoefficientDerived (pullback.fst a b ≫ a)) :
    ((coefficientDerivedTensor (𝟙 S)).obj
      ((RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj K)).obj
        ((RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj L) ⟶
      (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj
        ((coefficientDerivedTensor (pullback.fst a b ≫ a)).obj K |>.obj L) :=
  (RingedSite.Hom.moduleDerivedAdjunction.{u} (fiberCoefficientHom a b)).relativeDerivedCupProduct
    (coefficientDerivedTensor (𝟙 S))
    (coefficientDerivedTensor (pullback.fst a b ≫ a))
    (fun P Q ↦ (pullbackTensorComparison a b).app (P, Q)) K L

/-- The canonical derived-to-underived comparison from the tensor of the two derived
coefficient pullbacks to the explicit coefficient tensor complex. -/
noncomputable def derivedToCoefficientTensor
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) :
    ((coefficientDerivedTensor (pullback.fst a b ≫ a)).obj
      ((RingedSite.Hom.modulePullbackDerived.{u} (leftCoefficientHom a b)).obj
        (coefficientObject a F))).obj
      ((RingedSite.Hom.modulePullbackDerived.{u} (rightCoefficientHom a b)).obj
        (coefficientObject b G)) ⟶ coefficientTensor a b F G :=
  (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _ _).map
      (Prod.mkHom
        (((RingedSite.Hom.modulePullbackToDerived.{u} (leftCoefficientHom a b)).totalLeftDerivedCounit
            (RingedSite.Hom.moduleLocalization.{u} (coefficientSite a))
            (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))).app
          ((HomotopyCategory.quotient _ (up ℤ)).obj
            ((Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex a).obj F)))
        (((RingedSite.Hom.modulePullbackToDerived.{u} (rightCoefficientHom a b)).totalLeftDerivedCounit
            (RingedSite.Hom.moduleLocalization.{u} (coefficientSite b))
            (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))).app
          ((HomotopyCategory.quotient _ (up ℤ)).obj
            ((Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex b).obj G)))) ≫
    @CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.counitAppOfComplex
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _
      (leftPullbackComplex a b F) (rightPullbackComplex a b G) _

/-- The derived-tensor counit followed by localization of the ordinary
external-product comparison. -/
noncomputable def derivedExternalToTotal
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    ((coefficientDerivedTensor (pullback.fst a b ≫ a)).obj
      ((RingedSite.Hom.modulePullbackDerived.{u} (leftCoefficientHom a b)).obj
        (coefficientObject a F))).obj
      ((RingedSite.Hom.modulePullbackDerived.{u} (rightCoefficientHom a b)).obj
        (coefficientObject b G)) ⟶ externalTotal a b T hT F G :=
  derivedToCoefficientTensor a b F G ≫
    (RingedSite.Hom.moduleLocalization (coefficientSite (pullback.fst a b ≫ a))).map
      ((HomotopyCategory.quotient _ (up ℤ)).map (externalComparison a b T hT F G))

/-- The comparison to the ordinary external total is the composite of the
derived-to-coefficient-tensor map and the localized external comparison. -/
theorem derivedExternalToTotal_eq
    [(leftCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [(rightCoefficientHom a b).modulePushforward.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (leftCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite a))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u} (rightCoefficientHom a b))
      (RingedSite.Hom.ModuleQis.{u} (coefficientSite b))]
    [@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
      (RingedSite.ModuleCat.{u} (coefficientSite (pullback.fst a b ≫ a))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        (coefficientSite (pullback.fst a b ≫ a))) _ _ _ _ _ _ _]
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    derivedExternalToTotal a b T hT F G =
      derivedToCoefficientTensor a b F G ≫
        (RingedSite.Hom.moduleLocalization
          (coefficientSite (pullback.fst a b ≫ a))).map
          ((HomotopyCategory.quotient _ (up ℤ)).map
            (externalComparison a b T hT F G)) := sorry

section

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
  [PullbackTensorTargetIsLeftDerived a b]

/-- The canonical relative cup-product map from the derived tensor of the two direct
images to the direct image of the ordinary external-product total. -/
noncomputable def map
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    ((coefficientDerivedTensor (𝟙 S)).obj
      ((RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom a)).obj
        (coefficientObject a F))).obj
      ((RingedSite.Hom.modulePushforwardDerived.{u} (coefficientPushforwardHom b)).obj
        (coefficientObject b G)) ⟶
      (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).obj
        (externalTotal a b T hT F G) :=
  (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
      (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
      _ _ _ _ _ _ _ _).map
      (Prod.mkHom (leftLeg a b F) (rightLeg a b G)) ≫
    cupProduct a b
      ((RingedSite.Hom.modulePullbackDerived.{u} (leftCoefficientHom a b)).obj
        (coefficientObject a F))
      ((RingedSite.Hom.modulePullbackDerived.{u} (rightCoefficientHom a b)).obj
        (coefficientObject b G)) ≫
    (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).map
      (derivedExternalToTotal a b T hT F G)

/-- The relative cup-product map is the composite of its two canonical legs, the
relative derived cup product, and the comparison from the derived external tensor
to the ordinary external total. -/
theorem map_eq
    (T : Hom.FiniteOrderDifferentialOperatorCat a ⥤
      Hom.FiniteOrderDifferentialOperatorCat b ⥤
        Hom.FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : Hom.IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ)
    [HomologicalComplex.HasMapBifunctor F G T (up ℤ)] :
    map a b T hT F G =
      (@CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
        (RingedSite.ModuleCat.{u} (coefficientSite (𝟙 S))) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory (coefficientSite (𝟙 S)))
        _ _ _ _ _ _ _ _).map
        (Prod.mkHom (leftLeg a b F) (rightLeg a b G)) ≫
      cupProduct a b
        ((RingedSite.Hom.modulePullbackDerived.{u} (leftCoefficientHom a b)).obj
          (coefficientObject a F))
        ((RingedSite.Hom.modulePullbackDerived.{u} (rightCoefficientHom a b)).obj
          (coefficientObject b G)) ≫
      (RingedSite.Hom.modulePushforwardDerived.{u} (fiberCoefficientHom a b)).map
        (derivedExternalToTotal a b T hT F G) := sorry

end

end AlgebraicGeometry.Scheme.RelativeCupProduct

end
