/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.TensorPushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- The canonical comparison from derived pullback of a localized complex to the localization
of its ordinary termwise pullback. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackComplexComparison :
  ∀ {X' X : Scheme.{u}} (g' : X' ⟶ X) (G : CochainComplex X.Modules ℤ),
    (RingedSpace.modulePullbackDerived g'.toShHom).obj (DerivedCategory.Q.obj G) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex (up ℤ)).obj G))

/- The computation rule for the comparison from derived pullback to termwise pullback. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackComplexComparison_eq_counit :
  ∀ {X' X : Scheme.{u}} (g' : X' ⟶ X) (G : CochainComplex X.Modules ℤ),
    pullbackComplexComparison g' G =
      (RingedSpace.modulePullbackDerived g'.toShHom).map
          ((DerivedCategory.quotientCompQhIso X.Modules).inv.app G) ≫
        ((RingedSpace.modulePullbackToDerived g'.toShHom).totalLeftDerivedCounit
          DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
            ((HomotopyCategory.quotient X.Modules (up ℤ)).obj G) ≫
        (DerivedCategory.quotientCompQhIso X'.Modules).hom.app
          (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex (up ℤ)).obj G))

/- The tensor-pushforward base-change comparison with explicit ambient tensor models. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.tensorPushforwardBaseChangeMap :
  ∀ {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (T_X : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)
    (E : ModuleDerived.Quasicoherent X) (G : CochainComplex X.Modules ℤ),
    (RingedSpace.modulePullbackDerived g.toShHom).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (DerivedTensor.Right.obj E.obj (DerivedCategory.Q.obj G))) ⟶
      (RingedSpace.moduleDerivedPushforward f'.toShHom).obj
        (DerivedTensor.Right.obj
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj)
          (DerivedCategory.Q.obj
            (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
              (up ℤ)).obj G))))

/- The computation rule for the tensor-pushforward base-change comparison. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.tensorPushforwardBaseChangeMap_def :
  ∀ {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (T_X : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)
    (E : ModuleDerived.Quasicoherent X) (G : CochainComplex X.Modules ℤ),
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
                  (up ℤ)).obj G))).inv))

end AlgebraicGeometry.Scheme.DerivedQCoh

end
