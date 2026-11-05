/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.BaseChange.RestrictedPullback

@[expose] public section

/-! # Derived support, upper bounds, and base-change squares -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open SheafOfModules.ClosedSubset
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

noncomputable section
universe u

namespace ModuleCech.BaseChange

/-- The derived module of sections supported on the common zero locus of `f`. -/
noncomputable abbrev supportedObject {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) :=
  (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
    (ModuleCech.ofSectionsZeroLocus f)).obj ((ModuleCech.moduleToDerived X).obj ℱ)

/-- `supportedObject` is obtained by applying derived sections with support to the coefficient
module in degree zero. -/
theorem supportedObject_def {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    supportedObject f ℱ =
      (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).obj
          ((ModuleCech.moduleToDerived X).obj ℱ) := sorry

/-- The ambient direct image of `supportedObject`. -/
noncomputable abbrev pushedSupportedObject {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) : RingedSpace.ModuleDerived X.toRingedSpace :=
  (Derived.pushforward X.toRingedSpace.ringCatSheaf
    (ModuleCech.ofSectionsZeroLocus f)).obj (supportedObject f ℱ)

/-- `pushedSupportedObject` is the derived closed-subset direct image of `supportedObject`. -/
theorem pushedSupportedObject_def {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    pushedSupportedObject f ℱ =
      (Derived.pushforward X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).obj (supportedObject f ℱ) := sorry

/-- The derived supported object for `f` is bounded above by the length `c` of the equation
family when the coefficient sheaf is quasicoherent. -/
theorem pushedLocalCohomology_isLE {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (pushedSupportedObject f ℱ).IsLE (c : ℤ) := sorry

/-- In the intrinsic closed-subspace presentation, the supported object for a quasicoherent
module is bounded above by the length of the equation family. -/
theorem restrictedLocalCohomology_isLE {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj
        (supportedObject f ℱ)).IsLE (c : ℤ) := sorry

/-- The derived extended Čech complex for `c` equations is bounded above by degree `c`. -/
theorem ofSectionsDerived_isLE {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ).IsLE (c : ℤ) := sorry

/-- The supported base-change arrow followed by the coefficient comparison on sections with
support. This is the upper composite in the derived Čech base-change diagram. -/
noncomputable def supportMap {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    {closedPullback :
      ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⥤
        ModuleDerived X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))}
    (squareIso :
      closedPullback ⋙ Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom) :
    (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).obj
        (((ModuleCech.moduleToDerived X ⋙
          Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f)) ⋙
          Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f)).obj ℱ) ⟶
      (((ModuleCech.moduleToDerived X' ⋙
          Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))) ⋙
          Derived.pushforward X'.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).obj
        ((Scheme.Modules.pullback g).obj ℱ)) :=
  squareIso.inv.app
      ((Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).obj ((ModuleCech.moduleToDerived X).obj ℱ)) ≫
    (Derived.pushforward X'.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).map
        (DerivedBaseChange.app
            (Derived.adjunction X.toRingedSpace.ringCatSheaf
              (ModuleCech.ofSectionsZeroLocus f))
            (Derived.adjunction X'.toRingedSpace.ringCatSheaf
              (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
            squareIso ((ModuleCech.moduleToDerived X).obj ℱ) ≫
          (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).map
              (coefficientComparison g ℱ))

/-- `supportMap` is the closed-support derived base-change component followed by sections with
support of `coefficientComparison`. -/
theorem supportMap_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    {closedPullback :
      ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⥤
        ModuleDerived X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))}
    (squareIso :
      closedPullback ⋙ Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom) :
    supportMap g f ℱ squareIso =
      squareIso.inv.app
          ((Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f)).obj
              ((ModuleCech.moduleToDerived X).obj ℱ)) ≫
        (Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).map
            (DerivedBaseChange.app
                (Derived.adjunction X.toRingedSpace.ringCatSheaf
                  (ModuleCech.ofSectionsZeroLocus f))
                (Derived.adjunction X'.toRingedSpace.ringCatSheaf
                  (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))))
                squareIso ((ModuleCech.moduleToDerived X).obj ℱ) ≫
              (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf
                (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).map
                  (coefficientComparison g ℱ)) := sorry

/-- The supported comparison followed by the target counit is the pulled-back source counit
followed by the coefficient comparison. -/
theorem supportMap_comp_counit {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    {closedPullback :
      ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⥤
        ModuleDerived X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))}
    (squareIso :
      closedPullback ⋙ Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom) :
    supportMap g f ℱ squareIso ≫
        (Derived.adjunction X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))).counit.app
            ((ModuleCech.moduleToDerived X').obj ((Scheme.Modules.pullback g).obj ℱ)) =
      (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
          ((Derived.adjunction X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f)).counit.app
              ((ModuleCech.moduleToDerived X).obj ℱ)) ≫
        coefficientComparison g ℱ := sorry

/-- The direct closed-subset support map attached to pullback along
`RingedSpace.ClosedSubset.restrictedHom`. The square comparison is explicit because it records
the chosen derived realization of the geometric inverse-image square. -/
noncomputable def restrictedSupportMap {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z')
    (squareIso :
      restrictedDerivedPullbackTo g f hZ ⋙
          Derived.pushforward X'.toRingedSpace.ringCatSheaf Z' ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom) :
    (restrictedDerivedPullbackTo g f hZ).obj (supportedObject f ℱ) ⟶
      (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf Z').obj
        ((ModuleCech.moduleToDerived X').obj ((Scheme.Modules.pullback g).obj ℱ)) :=
  DerivedBaseChange.app
      (Derived.adjunction X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f))
      (Derived.adjunction X'.toRingedSpace.ringCatSheaf Z')
      squareIso ((ModuleCech.moduleToDerived X).obj ℱ) ≫
    (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf Z').map
      (coefficientComparison g ℱ)

/-- `restrictedSupportMap` is the derived closed-support mate followed by the coefficient
comparison on the target zero locus. -/
theorem restrictedSupportMap_def {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z')
    (squareIso :
      restrictedDerivedPullbackTo g f hZ ⋙
          Derived.pushforward X'.toRingedSpace.ringCatSheaf Z' ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom) :
    restrictedSupportMap g f ℱ hZ squareIso =
      DerivedBaseChange.app
          (Derived.adjunction X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f))
          (Derived.adjunction X'.toRingedSpace.ringCatSheaf Z')
          squareIso ((ModuleCech.moduleToDerived X).obj ℱ) ≫
        (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf Z').map
          (coefficientComparison g ℱ) := sorry

/-- The derived Čech/local-cohomology square specialized to pullback along the induced
morphism of the two zero loci. No quasicoherence hypothesis is used. -/
theorem restrictedDerivedCommSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    CommSq (derivedMap g f ℱ)
      ((RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
        ((ModuleCech.ofSectionsToLocalCohomology f).app ℱ))
      ((ModuleCech.ofSectionsToLocalCohomology
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))
      (supportMap g f ℱ (restrictedDerivedPushforwardIso g f)) := sorry

/-- The extended Čech comparison commutes with closed-support derived base change for every
module sheaf, without a quasicoherence hypothesis. -/
theorem derivedCommSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    {closedPullback :
      ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⥤
        ModuleDerived X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))}
    (squareIso :
      closedPullback ⋙ Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom) :
    CommSq (derivedMap g f ℱ)
      ((RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
        ((ModuleCech.ofSectionsToLocalCohomology f).app ℱ))
      ((ModuleCech.ofSectionsToLocalCohomology
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ))
      (supportMap g f ℱ squareIso) := sorry

/-- Applying degree-`c` homology to the derived commutative square gives the corresponding
homology square, without a quasicoherence hypothesis. -/
theorem derivedHomologyCommSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    {closedPullback :
      ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⥤
        ModuleDerived X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)))}
    (squareIso :
      closedPullback ⋙ Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
        Derived.pushforward X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f) ⋙
          RingedSpace.modulePullbackDerived g.toLRSHom.toShHom) :
    let H := DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)
    CommSq (H.map (derivedMap g f ℱ))
      (H.map ((RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
        ((ModuleCech.ofSectionsToLocalCohomology f).app ℱ)))
      (H.map ((ModuleCech.ofSectionsToLocalCohomology
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)))
      (H.map (supportMap g f ℱ squareIso)) := sorry

end ModuleCech.BaseChange
