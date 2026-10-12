/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Tensor

/-!
# Base change for tensor products and derived pushforwards

This module defines the comparison from derived pullback to ordinary termwise pullback and
uses it to construct the tensor-pushforward base-change morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X' X S' S : Scheme.{u}}

/-- The canonical comparison from derived pullback of the localization of a complex to the
localization of its ordinary termwise pullback. -/
noncomputable def pullbackComplexComparison (g' : X' ⟶ X)
    (G : CochainComplex X.Modules ℤ) :
    (RingedSpace.modulePullbackDerived g'.toShHom).obj (DerivedCategory.Q.obj G) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex (up ℤ)).obj G) :=
  (RingedSpace.modulePullbackDerived g'.toShHom).map
      ((DerivedCategory.quotientCompQhIso X.Modules).inv.app G) ≫
    ((RingedSpace.modulePullbackToDerived g'.toShHom).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
        ((HomotopyCategory.quotient X.Modules (up ℤ)).obj G) ≫
    (DerivedCategory.quotientCompQhIso X'.Modules).hom.app
      (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex (up ℤ)).obj G)

/-- The derived-to-termwise pullback comparison is the quotient comparison followed by the
total-left-derived counit and the target quotient comparison. -/
theorem pullbackComplexComparison_eq_counit (g' : X' ⟶ X)
    (G : CochainComplex X.Modules ℤ) :
    pullbackComplexComparison g' G =
      (RingedSpace.modulePullbackDerived g'.toShHom).map
          ((DerivedCategory.quotientCompQhIso X.Modules).inv.app G) ≫
        ((RingedSpace.modulePullbackToDerived g'.toShHom).totalLeftDerivedCounit
          DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
            ((HomotopyCategory.quotient X.Modules (up ℤ)).obj G) ≫
        (DerivedCategory.quotientCompQhIso X'.Modules).hom.app
          (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex (up ℤ)).obj G) := sorry

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends X'.toRingedSpace]
variable [KFlat.TensorDescends X'.toRingedSpace]
variable [KFlat.IsLocalization X'.toRingedSpace]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f'.toShHom)]
variable [IsIso
  (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
variable [IsIso
  (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
variable [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]

/-- The canonical base-change morphism for the derived pushforward of `E ⊗ᴸ Q(G)`, whose
target uses the ordinary termwise pullback of `G`. -/
noncomputable def tensorPushforwardBaseChangeMap
    (sq : IsPullback g' f' f g)
    (T_X : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)
    (E : ModuleDerived.Quasicoherent X) (G : CochainComplex X.Modules ℤ) :
    (RingedSpace.modulePullbackDerived g.toShHom).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G))) ⟶
      (RingedSpace.moduleDerivedPushforward f'.toShHom).obj
        (DerivedTensor.Right.obj
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj)
          (DerivedCategory.Q.obj
            (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
              (up ℤ)).obj G))) :=
  (Scheme.Hom.DerivedBaseChange.map sq.toCommSq).app
      (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
    (RingedSpace.moduleDerivedPushforward f'.toShHom).map
      ((RingedSpace.modulePullbackDerived g'.toShHom).map
          (T_X.objIsoTensor E.obj (DerivedCategory.Q.obj G)).hom ≫
        (Functor.Monoidal.μIso
          (RingedSpace.modulePullbackDerived g'.toShHom)
          E.obj (DerivedCategory.Q.obj G)).symm.hom ≫
        (𝟙 ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj) ⊗ₘ
          pullbackComplexComparison g' G) ≫
        (T_X'.objIsoTensor
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj)
          (DerivedCategory.Q.obj
            (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
              (up ℤ)).obj G))).inv)

/-- The tensor-pushforward base-change morphism is derived base change followed by
pushforward of the monoidal pullback comparison and the ordinary-complex pullback comparison. -/
theorem tensorPushforwardBaseChangeMap_def
    (sq : IsPullback g' f' f g)
    (T_X : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)
    (E : ModuleDerived.Quasicoherent X) (G : CochainComplex X.Modules ℤ) :
    tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X' E G =
      (Scheme.Hom.DerivedBaseChange.map sq.toCommSq).app
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G)) ≫
        (RingedSpace.moduleDerivedPushforward f'.toShHom).map
          ((RingedSpace.modulePullbackDerived g'.toShHom).map
              (T_X.objIsoTensor E.obj (DerivedCategory.Q.obj G)).hom ≫
            (Functor.Monoidal.μIso
              (RingedSpace.modulePullbackDerived g'.toShHom)
              E.obj (DerivedCategory.Q.obj G)).symm.hom ≫
            (𝟙 ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj) ⊗ₘ
              pullbackComplexComparison g' G) ≫
            (T_X'.objIsoTensor
              ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj)
              (DerivedCategory.Q.obj
                (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
                  (up ℤ)).obj G))).inv) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
