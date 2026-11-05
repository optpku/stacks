/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.BaseChange.DerivedSupport

@[expose] public section

/-! # Supported cohomology base change and Čech pullback comparison -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open SheafOfModules.ClosedSubset
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

noncomputable section
universe u

namespace ModuleCech.BaseChange

/-- The canonical degree-`c` supported base-change map after direct image. It is obtained from
the upper-edge pullback comparison, `supportMap`, and exactness of closed-subset pushforward. -/
noncomputable def supportedBaseChange {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
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
    (hE : (pushedSupportedObject f ℱ).IsLE (c : ℤ))
    [IsIso (singlePullbackHomologyComparison g.toLRSHom.toShHom
      ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).obj
        (pushedSupportedObject f ℱ)) (c : ℤ))]
    [IsIso ((DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)).map
      ((RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
        (upperCohomologyProjection (pushedSupportedObject f ℱ) (c : ℤ) hE)))] :
    (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
        ((ModuleCech.LocalCohomology.cohomologyFunctor f ⋙
          SheafOfModules.ClosedSubset.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f)).obj ℱ) ⟶
      ((ModuleCech.LocalCohomology.cohomologyFunctor
        (fun i ↦ g.appTop.hom (f i)) ⋙
          SheafOfModules.ClosedSubset.pushforward X'.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).obj
        ((Scheme.Modules.pullback g).obj ℱ)) :=
  let sourceSupport :=
    (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f)).obj ((ModuleCech.moduleToDerived X).obj ℱ)
  let targetSupport :=
    (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).obj
        ((ModuleCech.moduleToDerived X').obj ((Scheme.Modules.pullback g).obj ℱ))
  let sourcePushed :=
    (Derived.pushforward X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f)).obj sourceSupport
  let H := DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)
  let targetPushforwardExact := ExactFunctor.of
    (SheafOfModules.ClosedSubset.pushforward X'.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
  (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
      (((ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward
        X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f))).homologyFunctorIso
            (c : ℤ)).inv.app sourceSupport) ≫
    upperPullbackComparison g.toLRSHom.toShHom sourcePushed (c : ℤ)
      hE ≫
    H.map (supportMap g f ℱ squareIso) ≫
    (targetPushforwardExact.homologyFunctorIso (c : ℤ)).hom.app targetSupport

/-- `supportedBaseChange` is the degree-`c` map induced by the derived support comparison and
the canonical upper-edge and pushforward-homology identifications. -/
theorem supportedBaseChange_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
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
    (hE : (pushedSupportedObject f ℱ).IsLE (c : ℤ))
    [IsIso (singlePullbackHomologyComparison g.toLRSHom.toShHom
      ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).obj
        (pushedSupportedObject f ℱ)) (c : ℤ))]
    [IsIso ((DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)).map
      ((RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
        (upperCohomologyProjection (pushedSupportedObject f ℱ) (c : ℤ) hE)))] :
    supportedBaseChange g f ℱ squareIso hE =
      let sourceSupport :=
        (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f)).obj ((ModuleCech.moduleToDerived X).obj ℱ)
      let targetSupport :=
        (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).obj
            ((ModuleCech.moduleToDerived X').obj ((Scheme.Modules.pullback g).obj ℱ))
      let sourcePushed :=
        (Derived.pushforward X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f)).obj sourceSupport
      let H := DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)
      let targetPushforwardExact := ExactFunctor.of
        (SheafOfModules.ClosedSubset.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
      (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          (((ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward
            X.toRingedSpace.ringCatSheaf
              (ModuleCech.ofSectionsZeroLocus f))).homologyFunctorIso
                (c : ℤ)).inv.app sourceSupport) ≫
        upperPullbackComparison g.toLRSHom.toShHom sourcePushed (c : ℤ)
          hE ≫
        H.map (supportMap g f ℱ squareIso) ≫
        (targetPushforwardExact.homologyFunctorIso (c : ℤ)).hom.app targetSupport := sorry

/-- The degree-`c` supported base-change morphism in the closed-subset module category for the
induced morphism of the two zero loci. Boundedness and both inverse-using comparison facts are
explicit inputs to this concrete map. -/
noncomputable def restrictedSupportedBaseChange {X X' : Scheme.{u}}
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
    (restrictedPullbackTo g f hZ).obj
        ((ModuleCech.LocalCohomology.cohomologyFunctor f).obj ℱ) ⟶
      (ModuleCech.LocalCohomology.cohomologyFunctor
        (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ) :=
  restrictedUpperPullbackComparisonTo g f hZ (supportedObject f ℱ) (c : ℤ) hE ≫
    (DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.Modules X'.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
      (c : ℤ)).map (restrictedSupportMap g f ℱ hZ squareIso)

/-- `restrictedSupportedBaseChange` is the restricted upper-edge comparison followed by
degree-`c` homology of the direct closed-support base-change map. -/
theorem restrictedSupportedBaseChange_def {X X' : Scheme.{u}}
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
    restrictedSupportedBaseChange g f ℱ hZ squareIso hE =
      restrictedUpperPullbackComparisonTo g f hZ
          (supportedObject f ℱ) (c : ℤ) hE ≫
        (DerivedCategory.homologyFunctor
          (RingedSpace.ClosedSubset.Modules X'.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
          (c : ℤ)).map (restrictedSupportMap g f ℱ hZ squareIso) := sorry

/-- The canonical degree-`c` pullback map on Čech cohomology, obtained from the upper-edge
comparison and the explicit derived Čech map. -/
noncomputable def cechPullback {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (hE : ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ).IsLE (c : ℤ))
    [IsIso (singlePullbackHomologyComparison g.toLRSHom.toShHom
      ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).obj
        ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ)) (c : ℤ))]
    [IsIso ((DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)).map
      ((RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
        (upperCohomologyProjection ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ)
          (c : ℤ) hE)))] :
    (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
        ((ModuleCech.LocalCohomology.cechCohomologyFunctor f).obj ℱ) ⟶
      (ModuleCech.LocalCohomology.cechCohomologyFunctor
        (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ) :=
  let H := DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)
  (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
      ((ModuleCech.LocalCohomology.cechDerivedHomologyIso f).inv.app ℱ) ≫
    upperPullbackComparison g.toLRSHom.toShHom
      ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ) (c : ℤ)
        hE ≫
    H.map (derivedMap g f ℱ) ≫
    (ModuleCech.LocalCohomology.cechDerivedHomologyIso
      (fun i ↦ g.appTop.hom (f i))).hom.app ((Scheme.Modules.pullback g).obj ℱ)

/-- `cechPullback` is induced by the explicit derived Čech base-change map through the canonical
upper-edge and derived-to-ordinary homology comparisons. -/
theorem cechPullback_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (hE : ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ).IsLE (c : ℤ))
    [IsIso (singlePullbackHomologyComparison g.toLRSHom.toShHom
      ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).obj
        ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ)) (c : ℤ))]
    [IsIso ((DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)).map
      ((RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
        (upperCohomologyProjection ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ)
          (c : ℤ) hE)))] :
    cechPullback g f ℱ hE =
      let H := DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)
      (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          ((ModuleCech.LocalCohomology.cechDerivedHomologyIso f).inv.app ℱ) ≫
        upperPullbackComparison g.toLRSHom.toShHom
          ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ) (c : ℤ)
            hE ≫
        H.map (derivedMap g f ℱ) ≫
        (ModuleCech.LocalCohomology.cechDerivedHomologyIso
          (fun i ↦ g.appTop.hom (f i))).hom.app ((Scheme.Modules.pullback g).obj ℱ) := sorry

/-- The canonical Čech and supported base-change maps commute with the degree-`c` comparison
from the extended Čech complex to local cohomology. -/
theorem comparison_pullback_commSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
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
    (hCech : ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ).IsLE (c : ℤ))
    (hSupport : (pushedSupportedObject f ℱ).IsLE (c : ℤ)) :
    CommSq
      ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
        ((ModuleCech.LocalCohomology.comparison f).app ℱ))
      (cechPullback g f ℱ hCech) (supportedBaseChange g f ℱ squareIso hSupport)
      ((ModuleCech.LocalCohomology.comparison
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) := sorry

end ModuleCech.BaseChange
