/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Complex
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.FiniteOrder

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- Forget a finite-order differential operator relative to `a` to its underlying
`a⁻¹ᴼ_S`-linear morphism. -/
noncomputable def toCoefficientModules :
    FiniteOrderDifferentialOperatorCat a ⥤
      RingedSpace.DeRham.Modules.{u, u} a.toShHom where
  obj F := (restrictionAlong (coefficientMap a)).obj (underlying a F)
  map D := homToHom a D
  map_id F := homToHom_id a F
  map_comp D E := homToHom_comp a D E

/-- The coefficient-module realization preserves zero morphisms. -/
instance toCoefficientModules_preservesZeroMorphisms :
    (toCoefficientModules a).PreservesZeroMorphisms := sorry

/-- Apply the coefficient-module realization degreewise to a relative
finite-order differential-operator complex. -/
noncomputable abbrev toCoefficientComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCat a) ℤ ⥤
      CochainComplex (RingedSpace.DeRham.Modules.{u, u} a.toShHom) ℤ :=
  (toCoefficientModules a).mapHomologicalComplex (up ℤ)

/-- The coefficient realization has the expected object in every degree. -/
theorem toCoefficientComplex_X
    (F : CochainComplex (FiniteOrderDifferentialOperatorCat a) ℤ) (n : ℤ) :
    ((toCoefficientComplex a).obj F).X n =
      (restrictionAlong (coefficientMap a)).obj (underlying a (F.X n)) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat

namespace AlgebraicGeometry.Scheme.Modules.Kunneth

/-- The coefficient ringed site associated to a scheme morphism. -/
abbrev coefficientSite {X S : Scheme.{u}} (a : X ⟶ S) :=
  RingedSpace.DeRham.coefficientSite a.toShHom

/-- The derived category of modules over the inverse-image coefficient sheaf of a
scheme morphism. -/
abbrev CoefficientDerived {X S : Scheme.{u}} (a : X ⟶ S) :=
  RingedSite.Hom.ModuleDerived.{u} (coefficientSite a)

/-- A relative finite-order differential-operator complex, realized in the derived
category of modules over its inverse-image coefficient sheaf. -/
abbrev coefficientObject {X S : Scheme.{u}} (a : X ⟶ S)
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ) :
    CoefficientDerived a :=
  (RingedSite.Hom.moduleLocalization (coefficientSite a)).obj
    ((HomotopyCategory.quotient _ (up ℤ)).obj
      ((Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex a).obj F))

/-- Commutativity of the tautological coefficient square associated to `a`. -/
theorem coefficientPushforwardSquare_comm {X S : Scheme.{u}} (a : X ⟶ S) :
    a.toShHom ≫ 𝟙 S.toRingedSpace = a.toShHom ≫ 𝟙 S.toRingedSpace := sorry

/-- The tautological square presenting direct image from the coefficient site of `a`
to the coefficient site of `𝟙 S`. -/
theorem coefficientPushforwardSquare {X S : Scheme.{u}} (a : X ⟶ S) :
    CommSq a.toShHom a.toShHom (𝟙 S.toRingedSpace) (𝟙 S.toRingedSpace) := sorry

/-- The coefficient-site morphism whose derived direct image realizes `R(a)_*`. -/
noncomputable abbrev coefficientPushforwardHom {X S : Scheme.{u}} (a : X ⟶ S) :=
  RingedSpace.DeRham.baseChangeHom (coefficientPushforwardSquare a)

/-- Commutativity of the coefficient square associated to the first fiber-product projection. -/
theorem leftCoefficientSquare_comm {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    (pullback.fst a b).toShHom ≫ a.toShHom =
      (pullback.fst a b ≫ a).toShHom ≫ 𝟙 S.toRingedSpace := sorry

/-- The pullback square from `X ×_S Y` to `X`, with base map `𝟙 S`. -/
theorem leftCoefficientSquare {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    CommSq (pullback.fst a b).toShHom (pullback.fst a b ≫ a).toShHom
      a.toShHom (𝟙 S.toRingedSpace) := sorry

/-- Commutativity of the coefficient square associated to the second fiber-product projection. -/
theorem rightCoefficientSquare_comm {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    (pullback.snd a b).toShHom ≫ b.toShHom =
      (pullback.fst a b ≫ a).toShHom ≫ 𝟙 S.toRingedSpace := sorry

/-- The pullback square from `X ×_S Y` to `Y`, with base map `𝟙 S`. -/
theorem rightCoefficientSquare {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    CommSq (pullback.snd a b).toShHom (pullback.fst a b ≫ a).toShHom
      b.toShHom (𝟙 S.toRingedSpace) := sorry

/-- The coefficient-site inverse-image morphism associated to the first fiber-product
projection. -/
noncomputable abbrev leftCoefficientHom {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :=
  RingedSpace.DeRham.baseChangeHom (leftCoefficientSquare a b)

/-- The coefficient-site inverse-image morphism associated to the second fiber-product
projection. -/
noncomputable abbrev rightCoefficientHom {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :=
  RingedSpace.DeRham.baseChangeHom (rightCoefficientSquare a b)

/-- The coefficient-site morphism from the fiber product to the base, presented through the
first projection. -/
noncomputable abbrev fiberCoefficientHom {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :=
  (leftCoefficientHom a b).comp (coefficientPushforwardHom a)

/-- The coefficient-site morphism from the fiber product to the base, presented through the
second projection. -/
noncomputable abbrev rightFiberCoefficientHom {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) :=
  (rightCoefficientHom a b).comp (coefficientPushforwardHom b)

/-- The presentation of the fiber-product coefficient morphism through the second projection
agrees with the presentation through the first projection. -/
theorem rightFiberCoefficientHom_eq {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    rightFiberCoefficientHom a b = fiberCoefficientHom a b := sorry

/-- The coefficient complex obtained by pulling the realization of `F` to the fiber product. -/
noncomputable abbrev leftPullbackComplex {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).IsRightAdjoint]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ) :=
  (RingedSite.Hom.modulePullbackComplex.{u} (leftCoefficientHom a b)).obj
    ((Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex a).obj F)

/-- The coefficient complex obtained by pulling the realization of `G` to the fiber product. -/
noncomputable abbrev rightPullbackComplex {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).IsRightAdjoint]
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) :=
  (RingedSite.Hom.modulePullbackComplex.{u} (rightCoefficientHom a b)).obj
    ((Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex b).obj G)

/-- The two presentations of the direct image of a pulled-back module in the left
coefficient square agree. -/
theorem leftPullbackPushforward_eq {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).IsRightAdjoint]
    (M : X.Modules) :
    (restrictionAlong (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).obj
        ((Scheme.Modules.pushforward (pullback.fst a b)).obj
          ((Scheme.Modules.pullback (pullback.fst a b)).obj M)) =
      (RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).obj
        ((restrictionAlong
          (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap
            (pullback.fst a b ≫ a))).obj
          ((Scheme.Modules.pullback (pullback.fst a b)).obj M)) := sorry

/-- The canonical comparison from coefficient pullback to the coefficient restriction of
ordinary scheme pullback along the first projection. -/
noncomputable def leftPullbackComparison {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).IsRightAdjoint]
    (M : X.Modules) :
    (RingedSite.Hom.modulePullback.{u} (leftCoefficientHom a b)).obj
        ((restrictionAlong (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).obj M) ⟶
      (restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap
          (pullback.fst a b ≫ a))).obj
        ((Scheme.Modules.pullback (pullback.fst a b)).obj M) :=
  (RingedSite.Hom.modulePullbackHomEquiv (leftCoefficientHom a b) _ _).symm
    ((restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst a b)).unit.app M) ≫
        eqToHom (leftPullbackPushforward_eq a b M))

/-- The two presentations of the direct image of a pulled-back module in the right
coefficient square agree. -/
theorem rightPullbackPushforward_eq {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).IsRightAdjoint]
    (M : Y.Modules) :
    (restrictionAlong (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap b)).obj
        ((Scheme.Modules.pushforward (pullback.snd a b)).obj
          ((Scheme.Modules.pullback (pullback.snd a b)).obj M)) =
      (RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).obj
        ((restrictionAlong
          (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap
            (pullback.fst a b ≫ a))).obj
          ((Scheme.Modules.pullback (pullback.snd a b)).obj M)) := sorry

/-- The canonical comparison from coefficient pullback to the coefficient restriction of
ordinary scheme pullback along the second projection. -/
noncomputable def rightPullbackComparison {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).IsRightAdjoint]
    (M : Y.Modules) :
    (RingedSite.Hom.modulePullback.{u} (rightCoefficientHom a b)).obj
        ((restrictionAlong (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap b)).obj M) ⟶
      (restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap
          (pullback.fst a b ≫ a))).obj
        ((Scheme.Modules.pullback (pullback.snd a b)).obj M) :=
  (RingedSite.Hom.modulePullbackHomEquiv (rightCoefficientHom a b) _ _).symm
    ((restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap b)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd a b)).unit.app M) ≫
        eqToHom (rightPullbackPushforward_eq a b M))

/-- The intermediate total complex of the two coefficient-module pullbacks on `X ×_S Y`. -/
noncomputable abbrev coefficientTensorComplex {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).IsRightAdjoint]
    [(RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).IsRightAdjoint]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) :=
  HomologicalComplex.tensorObj (leftPullbackComplex a b F) (rightPullbackComplex a b G)

/-- The tensor bicomplex of the two ordinary coefficient pullbacks admits its canonical total. -/
theorem coefficientTensorComplex_hasTotal {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).IsRightAdjoint]
    [(RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).IsRightAdjoint]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) :
    HomologicalComplex.HasMapBifunctor (leftPullbackComplex a b F)
      (rightPullbackComplex a b G)
      (MonoidalCategory.curriedTensor (RingedSpace.DeRham.Modules
        (pullback.fst a b ≫ a).toShHom)) (up ℤ) := sorry

/-- The derived object represented by the intermediate coefficient tensor complex. -/
noncomputable abbrev coefficientTensor {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).IsRightAdjoint]
    [(RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).IsRightAdjoint]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) :
    CoefficientDerived (pullback.fst a b ≫ a) :=
  (RingedSite.Hom.moduleLocalization (coefficientSite (pullback.fst a b ≫ a))).obj
    ((HomotopyCategory.quotient _ (up ℤ)).obj (coefficientTensorComplex a b F G))

/-- The intermediate coefficient tensor is obtained by localizing its explicit total complex. -/
theorem coefficientTensor_def {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S)
    [(RingedSite.Hom.modulePushforward.{u} (leftCoefficientHom a b)).IsRightAdjoint]
    [(RingedSite.Hom.modulePushforward.{u} (rightCoefficientHom a b)).IsRightAdjoint]
    (F : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat a) ℤ)
    (G : CochainComplex (Hom.FiniteOrderDifferentialOperatorCat b) ℤ) :
    coefficientTensor a b F G =
      (RingedSite.Hom.moduleLocalization (coefficientSite (pullback.fst a b ≫ a))).obj
        ((HomotopyCategory.quotient _ (up ℤ)).obj
          (coefficientTensorComplex a b F G)) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth

end
