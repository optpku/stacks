/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.BaseChange.RestrictedPullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.BaseChange.DerivedSupport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.BaseChange.CechComparison

@[expose] public section

/-! # Čech classes and fundamental class maps under base change -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open SheafOfModules.ClosedSubset
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

noncomputable section
universe u

namespace ModuleCech.BaseChange

/-- Pullback preserves the top Čech numerator term before passage to cycles and homology. -/
theorem numeratorTerm_pullback {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          (ModuleCech.LocalCohomology.numeratorTerm f ℱ) ≫
        (Scheme.Modules.toRingedSpace X').map ((complexMap g f ℱ).f c) =
      ModuleCech.LocalCohomology.numeratorTerm
        (fun i ↦ g.appTop.hom (f i)) ((Scheme.Modules.pullback g).obj ℱ) := sorry

/-- Compatible coefficient, quotient, and Čech pullback maps carry the quotient-descended top
Čech numerator class through a commutative square. -/
theorem cechClass_commSq_of_numerator {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (coefficientPullback :
      (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
          ((Scheme.Modules.toRingedSpace X).obj ℱ) ⟶
        (Scheme.Modules.toRingedSpace X').obj ((Scheme.Modules.pullback g).obj ℱ))
    (quotientPullback :
      (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
          ((ModuleCech.LocalCohomology.quotientFunctor f).obj ℱ) ⟶
        (ModuleCech.LocalCohomology.quotientFunctor
          (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ))
    (cechPullback :
      (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
          ((ModuleCech.LocalCohomology.cechCohomologyFunctor f).obj ℱ) ⟶
        (ModuleCech.LocalCohomology.cechCohomologyFunctor
          (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ))
    (quotientProjectionSq :
      CommSq
        ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          ((ModuleCech.LocalCohomology.quotientProjection f).app ℱ))
        coefficientPullback quotientPullback
        ((ModuleCech.LocalCohomology.quotientProjection
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)))
    (numeratorClassSq :
      CommSq
        ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          ((ModuleCech.LocalCohomology.numeratorClass f).app ℱ))
        coefficientPullback cechPullback
        ((ModuleCech.LocalCohomology.numeratorClass
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) :
    CommSq
      ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
        ((ModuleCech.LocalCohomology.cechClass f).app ℱ))
      quotientPullback cechPullback
      ((ModuleCech.LocalCohomology.cechClass
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) := sorry

/-- Pullback preserves the quotient-descended top Čech numerator class
`s ↦ [s / ∏ i, f i]` for the pulled-back family of equations. -/
theorem cechClass_pullback_commSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (hE : ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ).IsLE (c : ℤ)) :
    CommSq
      ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
        ((ModuleCech.LocalCohomology.cechClass f).app ℱ))
      (quotientPullback g f ℱ) (cechPullback g f ℱ hE)
      ((ModuleCech.LocalCohomology.cechClass
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) := sorry

/-- Compatible quotient-projection and quotient-class squares yield the class-map square after
closed-subset pushforward. -/
theorem classMap_commSq_of_quotient {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (closedPullback :
      SheafOfModules.ClosedSubset.Modules X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f) ⥤
        SheafOfModules.ClosedSubset.Modules X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
    (coefficientPullback :
      closedPullback.obj ((ModuleCech.LocalCohomology.pullbackFunctor f).obj ℱ) ⟶
        (ModuleCech.LocalCohomology.pullbackFunctor
          (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ))
    (supportedBaseChange :
      closedPullback.obj ((ModuleCech.LocalCohomology.cohomologyFunctor f).obj ℱ) ⟶
        (ModuleCech.LocalCohomology.cohomologyFunctor
          (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ))
    (quotientPullback :
      closedPullback.obj ((ModuleCech.LocalCohomology.zeroLocusPullback f).obj ℱ) ⟶
        (ModuleCech.LocalCohomology.zeroLocusPullback
          (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ))
    (quotientProjectionSq :
      CommSq
        (closedPullback.map
          ((ModuleCech.LocalCohomology.pullbackQuotientProjection f).app ℱ))
        coefficientPullback quotientPullback
        ((ModuleCech.LocalCohomology.pullbackQuotientProjection
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)))
    (quotientClassSq :
      CommSq
        (closedPullback.map ((ModuleCech.LocalCohomology.quotientClassMap f).app ℱ))
        quotientPullback supportedBaseChange
        ((ModuleCech.LocalCohomology.quotientClassMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) :
    let pushforward := SheafOfModules.ClosedSubset.pushforward
      X'.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
    CommSq
      (pushforward.map
        (closedPullback.map ((ModuleCech.LocalCohomology.classMap f).app ℱ)))
      (pushforward.map coefficientPullback) (pushforward.map supportedBaseChange)
      (pushforward.map ((ModuleCech.LocalCohomology.classMap
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) := sorry

/-- For a quasicoherent module, the class maps commute directly in the module category on the
pulled-back zero locus. The horizontal maps are the concrete pullbacks associated to
`RingedSpace.ClosedSubset.restrictedHom`. -/
theorem restrictedClassMap_commSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) =
      ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
    (squareIso :
      restrictedDerivedPullbackTo g f hZ ⋙
          Derived.pushforward X'.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom)
    (hE : ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
        (supportedObject f ℱ)).IsLE (c : ℤ))
    [IsIso (singlePullbackHomologyComparison
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.ringedSpace X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).Modules (c : ℤ)).obj
        ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
            (supportedObject f ℱ))) (c : ℤ))]
    [IsIso ((DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.ringedSpace X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).Modules (c : ℤ)).map
      ((RingedSpace.modulePullbackDerived
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).map
        (upperCohomologyProjection
          ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
              (supportedObject f ℱ)) (c : ℤ) hE)))] :
    CommSq
      ((restrictedPullbackTo g f hZ).map
        ((ModuleCech.LocalCohomology.classMap f).app ℱ))
      (restrictedCoefficientComparisonTo g f ℱ hZ (restrictedSquare g f))
      (restrictedSupportedBaseChange g f ℱ hZ squareIso
        (restrictedLocalCohomology_isLE f ℱ))
      ((ModuleCech.LocalCohomology.classMap
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) := sorry

/-- The source-form class-map square, using the canonical equality between the inverse-image
closed subset and the zero locus of the pulled-back equations. -/
theorem classMap_restricted_commSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    CommSq
      ((restrictedPullbackTo g f (zeroLocus_preimage g f)).map
        ((ModuleCech.LocalCohomology.classMap f).app ℱ))
      (restrictedCoefficientComparisonTo g f ℱ (zeroLocus_preimage g f)
        (restrictedSquare g f))
      (restrictedSupportedBaseChange g f ℱ (zeroLocus_preimage g f)
        (restrictedDerivedPushforwardIso g f) (restrictedLocalCohomology_isLE f ℱ))
      ((ModuleCech.LocalCohomology.classMap
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) := sorry

/-- The ambient pushed-forward class-map square obtained from the canonical direct restricted
square on the two zero loci. -/
theorem classMap_restricted_pushforward_commSq {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] :
    let pushforward := SheafOfModules.ClosedSubset.pushforward
      X'.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
    CommSq
      (pushforward.map ((restrictedPullbackTo g f (zeroLocus_preimage g f)).map
        ((ModuleCech.LocalCohomology.classMap f).app ℱ)))
      (pushforward.map (restrictedCoefficientComparisonTo g f ℱ
        (zeroLocus_preimage g f) (restrictedSquare g f)))
      (pushforward.map (restrictedSupportedBaseChange g f ℱ
        (zeroLocus_preimage g f) (restrictedDerivedPushforwardIso g f)
          (restrictedLocalCohomology_isLE f ℱ)))
      (pushforward.map ((ModuleCech.LocalCohomology.classMap
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) := sorry

/-- For the canonical restricted pullback maps, the direct class-map square commutes exactly
when its image under faithful closed-subset pushforward commutes. -/
theorem classMap_restricted_pushforward_bridge {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] :
    CommSq
        ((restrictedPullbackTo g f (zeroLocus_preimage g f)).map
          ((ModuleCech.LocalCohomology.classMap f).app ℱ))
        (restrictedCoefficientComparisonTo g f ℱ (zeroLocus_preimage g f)
          (restrictedSquare g f))
        (restrictedSupportedBaseChange g f ℱ (zeroLocus_preimage g f)
          (restrictedDerivedPushforwardIso g f) (restrictedLocalCohomology_isLE f ℱ))
        ((ModuleCech.LocalCohomology.classMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) ↔
      let pushforward := SheafOfModules.ClosedSubset.pushforward
        X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
      CommSq
        (pushforward.map ((restrictedPullbackTo g f (zeroLocus_preimage g f)).map
          ((ModuleCech.LocalCohomology.classMap f).app ℱ)))
        (pushforward.map (restrictedCoefficientComparisonTo g f ℱ
          (zeroLocus_preimage g f) (restrictedSquare g f)))
        (pushforward.map (restrictedSupportedBaseChange g f ℱ
          (zeroLocus_preimage g f) (restrictedDerivedPushforwardIso g f)
            (restrictedLocalCohomology_isLE f ℱ)))
        (pushforward.map ((ModuleCech.LocalCohomology.classMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) := sorry

/-- Faithful direct image carries the direct restricted class-map square to its ambient
pushed-forward square. -/
theorem restrictedClassMap_pushforward_commSq {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent]
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) =
      ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
    (squareIso :
      restrictedDerivedPullbackTo g f hZ ⋙
          Derived.pushforward X'.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom)
    (hE : ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
        (supportedObject f ℱ)).IsLE (c : ℤ))
    [IsIso (singlePullbackHomologyComparison
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.ringedSpace X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).Modules (c : ℤ)).obj
        ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
            (supportedObject f ℱ))) (c : ℤ))]
    [IsIso ((DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.ringedSpace X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).Modules (c : ℤ)).map
      ((RingedSpace.modulePullbackDerived
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).map
        (upperCohomologyProjection
          ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
              (supportedObject f ℱ)) (c : ℤ) hE)))] :
    let pushforward := SheafOfModules.ClosedSubset.pushforward
      X'.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
    CommSq
      (pushforward.map ((restrictedPullbackTo g f hZ).map
        ((ModuleCech.LocalCohomology.classMap f).app ℱ)))
      (pushforward.map
        (restrictedCoefficientComparisonTo g f ℱ hZ (restrictedSquare g f)))
      (pushforward.map (restrictedSupportedBaseChange g f ℱ hZ squareIso hE))
      (pushforward.map ((ModuleCech.LocalCohomology.classMap
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) := sorry

/-- The direct restricted class-map square commutes if and only if its image under faithful
closed-subset pushforward commutes; both sides use the same canonical restricted maps. -/
theorem restrictedClassMap_pushforward_bridge {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent]
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) =
      ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
    (squareIso :
      restrictedDerivedPullbackTo g f hZ ⋙
          Derived.pushforward X'.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom)
    (hE : ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
        (supportedObject f ℱ)).IsLE (c : ℤ))
    [IsIso (singlePullbackHomologyComparison
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.ringedSpace X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).Modules (c : ℤ)).obj
        ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
            (supportedObject f ℱ))) (c : ℤ))]
    [IsIso ((DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.ringedSpace X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).Modules (c : ℤ)).map
      ((RingedSpace.modulePullbackDerived
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).map
        (upperCohomologyProjection
          ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
              (supportedObject f ℱ)) (c : ℤ) hE)))] :
    CommSq
        ((restrictedPullbackTo g f hZ).map
          ((ModuleCech.LocalCohomology.classMap f).app ℱ))
        (restrictedCoefficientComparisonTo g f ℱ hZ (restrictedSquare g f))
        (restrictedSupportedBaseChange g f ℱ hZ squareIso hE)
        ((ModuleCech.LocalCohomology.classMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) ↔
      let pushforward := SheafOfModules.ClosedSubset.pushforward
        X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
      CommSq
        (pushforward.map ((restrictedPullbackTo g f hZ).map
          ((ModuleCech.LocalCohomology.classMap f).app ℱ)))
        (pushforward.map
          (restrictedCoefficientComparisonTo g f ℱ hZ (restrictedSquare g f)))
        (pushforward.map (restrictedSupportedBaseChange g f ℱ hZ squareIso hE))
        (pushforward.map ((ModuleCech.LocalCohomology.classMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) := sorry

/-- For a quasicoherent module, the two canonical class maps commute with the degree-`c`
supported base-change map after direct image to the ambient ringed space. -/
theorem classMap_pushforward_commSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {closedPullback :
      ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⥤
        ModuleDerived X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))}
    (squareIso :
      closedPullback ⋙ Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom)
    (hE : (pushedSupportedObject f ℱ).IsLE (c : ℤ)) :
    let sourcePushforward := SheafOfModules.ClosedSubset.pushforward
      X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)
    let targetPushforward := SheafOfModules.ClosedSubset.pushforward
      X'.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
    CommSq
      ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
        ((SheafOfModules.pullbackPushforwardAdjunction
          (SheafOfModules.ClosedSubset.structureMap X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f))).unit.app
              ((Scheme.Modules.toRingedSpace X).obj ℱ) ≫
          sourcePushforward.map ((ModuleCech.LocalCohomology.classMap f).app ℱ)))
      (coefficientPullback g ℱ) (supportedBaseChange g f ℱ squareIso hE)
      ((SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.ClosedSubset.structureMap X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))).unit.app
            ((Scheme.Modules.toRingedSpace X').obj ((Scheme.Modules.pullback g).obj ℱ)) ≫
        targetPushforward.map ((ModuleCech.LocalCohomology.classMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) := sorry

/-- Faithfulness of closed-subset pushforward identifies a direct class-map square with its
ambient pushed-forward square. -/
theorem classMap_pushforward_bridge {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (closedPullback :
      SheafOfModules.ClosedSubset.Modules X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f) ⥤
        SheafOfModules.ClosedSubset.Modules X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
    (coefficientPullback :
      closedPullback.obj ((ModuleCech.LocalCohomology.pullbackFunctor f).obj ℱ) ⟶
        (ModuleCech.LocalCohomology.pullbackFunctor
          (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ))
    (supportedBaseChange :
      closedPullback.obj ((ModuleCech.LocalCohomology.cohomologyFunctor f).obj ℱ) ⟶
        (ModuleCech.LocalCohomology.cohomologyFunctor
          (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ)) :
    CommSq (closedPullback.map ((ModuleCech.LocalCohomology.classMap f).app ℱ))
        coefficientPullback supportedBaseChange
        ((ModuleCech.LocalCohomology.classMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) ↔
      let pushforward := SheafOfModules.ClosedSubset.pushforward
        X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))
      CommSq
        (pushforward.map
          (closedPullback.map ((ModuleCech.LocalCohomology.classMap f).app ℱ)))
        (pushforward.map coefficientPullback) (pushforward.map supportedBaseChange)
        (pushforward.map ((ModuleCech.LocalCohomology.classMap
          (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))) := sorry

end ModuleCech.BaseChange
