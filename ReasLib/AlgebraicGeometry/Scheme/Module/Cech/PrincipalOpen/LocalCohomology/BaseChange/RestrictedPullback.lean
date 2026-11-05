/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.BaseChange.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology

@[expose] public section

/-! # Restricted pullback and finite-section quotient comparisons -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open SheafOfModules.ClosedSubset
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

noncomputable section
universe u

namespace ModuleCech.BaseChange

/-- Pullback along the morphism of closed ringed subspaces induced by `g`, transported to the
closed-subset module presentation used by the local-cohomology API. -/
noncomputable def restrictedPullback {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) :
    RingedSpace.ClosedSubset.Modules.{u, u} X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f) ⥤
      RingedSpace.ClosedSubset.Modules.{u, u} X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)) :=
  (RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).inverse ⋙
    RingedSpace.Hom.pullback
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f)) ⋙
    (RingedSpace.ClosedSubset.moduleEquivalence X'.toRingedSpace
      (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))).functor

/-- The restricted pullback is the intrinsic module pullback along
`RingedSpace.ClosedSubset.restrictedHom`, transported through the two presentation equivalences. -/
theorem restrictedPullback_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) :
    restrictedPullback g f =
      (RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f)).inverse ⋙
      RingedSpace.Hom.pullback
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)) ⋙
      (RingedSpace.ClosedSubset.moduleEquivalence X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).functor := sorry

/-- The restricted pullback, reindexed from the canonical inverse-image closed subset to a
specified equal closed subset. -/
noncomputable def restrictedPullbackTo {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z') :
    RingedSpace.ClosedSubset.Modules.{u, u} X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f) ⥤
      RingedSpace.ClosedSubset.Modules.{u, u} X'.toRingedSpace Z' :=
  match hZ with
  | rfl => restrictedPullback g f

/-- `restrictedPullbackTo` is transport of the intrinsic restricted pullback along the supplied
closed-subset equality. -/
theorem restrictedPullbackTo_def {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z') :
    restrictedPullbackTo g f hZ =
      match hZ with
      | rfl => restrictedPullback g f := sorry

/-- The restricted derived pullback, reindexed from the canonical inverse-image closed subset to
a specified equal closed subset. -/
noncomputable def restrictedDerivedPullbackTo {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z') :
    ModuleDerived X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⥤
      ModuleDerived X'.toRingedSpace.ringCatSheaf Z' :=
  hZ ▸ RingedSpace.ClosedSubset.InverseImage.derivedPullback g.toLRSHom.toShHom
    (ModuleCech.ofSectionsZeroLocus f)

/-- `restrictedDerivedPullbackTo` is transport of the intrinsic derived restricted pullback along
the supplied closed-subset equality. -/
theorem restrictedDerivedPullbackTo_def {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z') :
    restrictedDerivedPullbackTo g f hZ =
      hZ ▸ RingedSpace.ClosedSubset.InverseImage.derivedPullback g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) := sorry

/-- The canonical comparison from derived pullback of a module in degree zero to ordinary
pullback of that module in degree zero. -/
noncomputable def coefficientComparison {X X' : Scheme.{u}} (g : X' ⟶ X)
    (ℱ : X.Modules) :
    (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).obj
        ((ModuleCech.moduleToDerived X).obj ℱ) ⟶
      (ModuleCech.moduleToDerived X').obj ((Scheme.Modules.pullback g).obj ℱ) :=
  let K := ((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
    ((CochainComplex.single₀ X.Modules).obj ℱ)
  (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
      ((DerivedCategory.quotientCompQhIso X.toRingedSpace.Modules).inv.app
        (K.extend embeddingUpNat)) ≫
    ((RingedSpace.modulePullbackToDerived g.toLRSHom.toShHom).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
        ((HomotopyCategory.quotient X.toRingedSpace.Modules (up ℤ)).obj
          (K.extend embeddingUpNat)) ≫
    DerivedCategory.Q.map
      (ComplexShape.Embedding.mapAppIso embeddingUpNat
        (RingedSpace.Hom.pullback g.toLRSHom.toShHom) K).hom ≫
    (ModuleCech.toRingedSpaceDerived X').map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pullback g) (up ℕ) 0).hom.app ℱ)

/-- `coefficientComparison` is the total-left-derived counit followed by the canonical
change-of-coefficients and degree-zero identifications. -/
theorem coefficientComparison_def {X X' : Scheme.{u}} (g : X' ⟶ X)
    (ℱ : X.Modules) :
    coefficientComparison g ℱ =
      let K := ((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
        ((CochainComplex.single₀ X.Modules).obj ℱ)
      (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
          ((DerivedCategory.quotientCompQhIso X.toRingedSpace.Modules).inv.app
            (K.extend embeddingUpNat)) ≫
        ((RingedSpace.modulePullbackToDerived g.toLRSHom.toShHom).totalLeftDerivedCounit
          DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
            ((HomotopyCategory.quotient X.toRingedSpace.Modules (up ℤ)).obj
              (K.extend embeddingUpNat)) ≫
        DerivedCategory.Q.map
          (ComplexShape.Embedding.mapAppIso embeddingUpNat
            (RingedSpace.Hom.pullback g.toLRSHom.toShHom) K).hom ≫
        (ModuleCech.toRingedSpaceDerived X').map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pullback g) (up ℕ) 0).hom.app ℱ) := sorry

/-- The upper-edge comparison for pullback along the induced morphism of closed ringed
subspaces, expressed in the closed-subset module presentation. -/
noncomputable def restrictedUpperPullbackComparison {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (E : ModuleDerived X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f)) (i : ℤ)
    (hE : ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E).IsLE i)
    [IsIso (singlePullbackHomologyComparison
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.ringedSpace X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).Modules i).obj
        ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E)) i)]
    [IsIso ((DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.ringedSpace X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).Modules i).map
      ((RingedSpace.modulePullbackDerived
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).map
        (upperCohomologyProjection
          ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E) i hE)))] :
    (restrictedPullback g f).obj
        ((DerivedCategory.homologyFunctor
          (RingedSpace.ClosedSubset.Modules X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)) i).obj E) ⟶
      (DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.Modules X'.toRingedSpace
          (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
            (ModuleCech.ofSectionsZeroLocus f))) i).obj
        ((RingedSpace.ClosedSubset.InverseImage.derivedPullback g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)).obj E) :=
  let sourceEquiv := RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
    (ModuleCech.ofSectionsZeroLocus f)
  let targetEquiv := RingedSpace.ClosedSubset.moduleEquivalence X'.toRingedSpace
    (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
      (ModuleCech.ofSectionsZeroLocus f))
  let restricted := RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
    (ModuleCech.ofSectionsZeroLocus f)
  let intrinsicE := sourceEquiv.mapDerivedCategory.inverse.obj E
  targetEquiv.functor.map
      ((RingedSpace.Hom.pullback restricted).map
        ((Equivalence.MapDerivedCategory.inverseExact sourceEquiv).homologyFunctorIso i
          |>.inv.app E) ≫
        upperPullbackComparison restricted intrinsicE i hE) ≫
    ((Equivalence.MapDerivedCategory.forwardExact targetEquiv).homologyFunctorIso i
      |>.inv.app ((RingedSpace.modulePullbackDerived restricted).obj intrinsicE))

/-- `restrictedUpperPullbackComparison` is obtained from the intrinsic upper-edge comparison
and the homology comparisons for the two presentation equivalences. -/
theorem restrictedUpperPullbackComparison_def {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (E : ModuleDerived X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f)) (i : ℤ)
    (hE : ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E).IsLE i)
    [IsIso (singlePullbackHomologyComparison
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.ringedSpace X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).Modules i).obj
        ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E)) i)]
    [IsIso ((DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.ringedSpace X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).Modules i).map
      ((RingedSpace.modulePullbackDerived
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).map
        (upperCohomologyProjection
          ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E) i hE)))] :
    restrictedUpperPullbackComparison g f E i hE =
      let sourceEquiv := RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f)
      let targetEquiv := RingedSpace.ClosedSubset.moduleEquivalence X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))
      let restricted := RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f)
      let intrinsicE := sourceEquiv.mapDerivedCategory.inverse.obj E
      targetEquiv.functor.map
          ((RingedSpace.Hom.pullback restricted).map
            ((Equivalence.MapDerivedCategory.inverseExact sourceEquiv).homologyFunctorIso i
              |>.inv.app E) ≫
            upperPullbackComparison restricted intrinsicE i hE) ≫
        ((Equivalence.MapDerivedCategory.forwardExact targetEquiv).homologyFunctorIso i
          |>.inv.app ((RingedSpace.modulePullbackDerived restricted).obj intrinsicE)) := sorry

/-- The restricted upper-edge comparison transported to the zero locus of the pulled-back
equations. The equality argument records the canonical identification of this zero locus with
the inverse-image closed subset. -/
noncomputable def restrictedUpperPullbackComparisonTo {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z')
    (E : ModuleDerived X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f)) (i : ℤ)
    (hE : ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E).IsLE i)
    [IsIso (singlePullbackHomologyComparison
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.ringedSpace X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).Modules i).obj
        ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E)) i)]
    [IsIso ((DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.ringedSpace X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).Modules i).map
      ((RingedSpace.modulePullbackDerived
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).map
        (upperCohomologyProjection
          ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E) i hE)))] :
    (restrictedPullbackTo g f hZ).obj
        ((DerivedCategory.homologyFunctor
          (RingedSpace.ClosedSubset.Modules X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)) i).obj E) ⟶
      (DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.Modules X'.toRingedSpace
          Z') i).obj
        ((restrictedDerivedPullbackTo g f hZ).obj E) :=
  match hZ with
  | rfl => restrictedUpperPullbackComparison g f E i hE

/-- The transported restricted upper-edge comparison is the intrinsic comparison reindexed by
the equality of the two target closed subsets. -/
theorem restrictedUpperPullbackComparisonTo_def {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z')
    (E : ModuleDerived X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f)) (i : ℤ)
    (hE : ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
      (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E).IsLE i)
    [IsIso (singlePullbackHomologyComparison
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      ((DerivedCategory.homologyFunctor
        (RingedSpace.ClosedSubset.ringedSpace X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).Modules i).obj
        ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
          (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E)) i)]
    [IsIso ((DerivedCategory.homologyFunctor
      (RingedSpace.ClosedSubset.ringedSpace X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).Modules i).map
      ((RingedSpace.modulePullbackDerived
        (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).map
        (upperCohomologyProjection
          ((RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
            (ModuleCech.ofSectionsZeroLocus f)).mapDerivedCategory.inverse.obj E) i hE)))] :
    restrictedUpperPullbackComparisonTo g f hZ E i hE =
      match hZ with
      | rfl => restrictedUpperPullbackComparison g f E i hE := sorry

/-- Ordinary pullback of a scheme module agrees with the underlying ringed-space pullback. -/
noncomputable def coefficientPullback {X X' : Scheme.{u}} (g : X' ⟶ X)
    (ℱ : X.Modules) :
    (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
        ((Scheme.Modules.toRingedSpace X).obj ℱ) ⟶
      (Scheme.Modules.toRingedSpace X').obj ((Scheme.Modules.pullback g).obj ℱ) :=
  𝟙 _

/-- The canonical commutative square formed by the induced morphism of inverse-image closed
subspaces and the two closed-subspace inclusions. -/
theorem restrictedSquare {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) :
    CommSq
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      (RingedSpace.ClosedSubset.inclusionHom X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)))
      (RingedSpace.ClosedSubset.inclusionHom X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f)) g.toLRSHom.toShHom := sorry

/-- The canonical derived-pushforward comparison for the zero locus of a pulled-back finite
family of global sections. -/
noncomputable def restrictedDerivedPushforwardIso {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    restrictedDerivedPullbackTo g f (zeroLocus_preimage g f) ⋙
        Derived.pushforward X'.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i))) ≅
      Derived.pushforward X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f) ⋙
        RingedSpace.modulePullbackDerived g.toLRSHom.toShHom :=
  let comparisonTo :
      ∀ {Z' : Closeds X'}
        (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f) = Z'),
        restrictedDerivedPullbackTo g f hZ ⋙
            Derived.pushforward X'.toRingedSpace.ringCatSheaf Z' ≅
          Derived.pushforward X.toRingedSpace.ringCatSheaf
              (ModuleCech.ofSectionsZeroLocus f) ⋙
            RingedSpace.modulePullbackDerived g.toLRSHom.toShHom :=
    fun {_} hZ =>
      match hZ with
      | rfl =>
          RingedSpace.ClosedSubset.InverseImage.derivedPushforwardIso
            g.toLRSHom.toShHom (ModuleCech.ofSectionsZeroLocus f)
  comparisonTo (zeroLocus_preimage g f)

/-- The canonical coefficient map for pullback along the induced morphism of inverse-image
closed subspaces. It is the inverse pullback-square comparison, transported through the two
closed-subset module equivalences. -/
noncomputable def restrictedCoefficientComparison {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (sq : CommSq
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      (RingedSpace.ClosedSubset.inclusionHom X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)))
      (RingedSpace.ClosedSubset.inclusionHom X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f)) g.toLRSHom.toShHom) :
    (restrictedPullback g f).obj
        ((ModuleCech.LocalCohomology.pullbackFunctor f).obj ℱ) ⟶
      (RingedSpace.ClosedSubset.pullback X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f))).obj
        ((Scheme.Modules.toRingedSpace X').obj ((Scheme.Modules.pullback g).obj ℱ)) :=
  let sourceEquiv := RingedSpace.ClosedSubset.moduleEquivalence X.toRingedSpace
    (ModuleCech.ofSectionsZeroLocus f)
  let targetEquiv := RingedSpace.ClosedSubset.moduleEquivalence X'.toRingedSpace
    (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
      (ModuleCech.ofSectionsZeroLocus f))
  let restricted := RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
    (ModuleCech.ofSectionsZeroLocus f)
  let sourceInclusion := RingedSpace.ClosedSubset.inclusionHom X.toRingedSpace
    (ModuleCech.ofSectionsZeroLocus f)
  let M := (Scheme.Modules.toRingedSpace X).obj ℱ
  targetEquiv.functor.map
      ((RingedSpace.Hom.pullback restricted).map
          (sourceEquiv.inverse.map
              ((RingedSpace.ClosedSubset.Inclusion.pullbackIso X.toRingedSpace
                (ModuleCech.ofSectionsZeroLocus f)).inv.app M) ≫
            sourceEquiv.unitIso.inv.app
              ((RingedSpace.Hom.pullback sourceInclusion).obj M)) ≫
        (RingedSpace.Hom.BaseChange.pullbackIso sq).inv.app M) ≫
    (RingedSpace.ClosedSubset.Inclusion.pullbackIso X'.toRingedSpace
      (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))).hom.app
          ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj M) ≫
    (RingedSpace.ClosedSubset.pullback X'.toRingedSpace
      (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))).map (coefficientPullback g ℱ)

/-- The restricted coefficient comparison is an isomorphism. -/
noncomputable instance restrictedCoefficientComparison_isIso {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (sq : CommSq
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      (RingedSpace.ClosedSubset.inclusionHom X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)))
      (RingedSpace.ClosedSubset.inclusionHom X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f)) g.toLRSHom.toShHom) :
    IsIso (restrictedCoefficientComparison g f ℱ sq) := sorry

/-- The coefficient comparison reindexed to the zero locus of the pulled-back equations. -/
noncomputable def restrictedCoefficientComparisonTo {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z')
    (sq : CommSq
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      (RingedSpace.ClosedSubset.inclusionHom X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)))
      (RingedSpace.ClosedSubset.inclusionHom X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f)) g.toLRSHom.toShHom) :
    (restrictedPullbackTo g f hZ).obj
        ((ModuleCech.LocalCohomology.pullbackFunctor f).obj ℱ) ⟶
      (RingedSpace.ClosedSubset.pullback X'.toRingedSpace Z').obj
        ((Scheme.Modules.toRingedSpace X').obj ((Scheme.Modules.pullback g).obj ℱ)) :=
  match hZ with
  | rfl => restrictedCoefficientComparison g f ℱ sq

/-- `restrictedCoefficientComparisonTo` is the intrinsic coefficient comparison transported
along the equality of the two target zero loci. -/
theorem restrictedCoefficientComparisonTo_def {X X' : Scheme.{u}}
    (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    {Z' : Closeds X'}
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) = Z')
    (sq : CommSq
      (RingedSpace.ClosedSubset.restrictedHom g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f))
      (RingedSpace.ClosedSubset.inclusionHom X'.toRingedSpace
        (RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
          (ModuleCech.ofSectionsZeroLocus f)))
      (RingedSpace.ClosedSubset.inclusionHom X.toRingedSpace
        (ModuleCech.ofSectionsZeroLocus f)) g.toLRSHom.toShHom) :
    restrictedCoefficientComparisonTo g f ℱ hZ sq =
      match hZ with
      | rfl => restrictedCoefficientComparison g f ℱ sq := sorry

/-- The canonical comparison from pullback of a finite direct sum to the corresponding direct
sum of pulled-back scheme modules. -/
noncomputable def sectionSumPullback {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (ℱ : X.Modules) :
    (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
        ((Scheme.Modules.toRingedSpace X).obj (⨁ (fun _ : Fin c ↦ ℱ))) ⟶
      (Scheme.Modules.toRingedSpace X').obj
        (⨁ (fun _ : Fin c ↦ (Scheme.Modules.pullback g).obj ℱ)) :=
  (Scheme.Modules.toRingedSpace X').map
    (Functor.biproductComparison (Scheme.Modules.pullback g) (fun _ : Fin c ↦ ℱ))

/-- Pullback of finite-family multiplication agrees with multiplication by the pulled-back
sections. -/
theorem sectionMultiplication_pullback {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          (ModuleCech.LocalCohomology.sectionMultiplication f ℱ) ≫
        coefficientPullback g ℱ =
      sectionSumPullback g ℱ ≫
        ModuleCech.LocalCohomology.sectionMultiplication
          (fun i ↦ g.appTop.hom (f i)) ((Scheme.Modules.pullback g).obj ℱ) := sorry

/-- The canonical pullback map on the finite-family quotients defining the class map. -/
noncomputable def quotientPullback {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (RingedSpace.Hom.pullback g.toLRSHom.toShHom).obj
        ((ModuleCech.LocalCohomology.quotientFunctor f).obj ℱ) ⟶
      (ModuleCech.LocalCohomology.quotientFunctor
        (fun i ↦ g.appTop.hom (f i))).obj ((Scheme.Modules.pullback g).obj ℱ) :=
  (PreservesCokernel.iso (RingedSpace.Hom.pullback g.toLRSHom.toShHom)
      (ModuleCech.LocalCohomology.sectionMultiplication f ℱ)).hom ≫
    cokernel.map
      ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
        (ModuleCech.LocalCohomology.sectionMultiplication f ℱ))
      (ModuleCech.LocalCohomology.sectionMultiplication
        (fun i ↦ g.appTop.hom (f i)) ((Scheme.Modules.pullback g).obj ℱ))
      (sectionSumPullback g ℱ) (coefficientPullback g ℱ)
      (sectionMultiplication_pullback g f ℱ)

/-- The quotient pullback map is the cokernel comparison followed by the map induced by
pullback compatibility of finite-family multiplication. -/
theorem quotientPullback_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    quotientPullback g f ℱ =
      (PreservesCokernel.iso (RingedSpace.Hom.pullback g.toLRSHom.toShHom)
        (ModuleCech.LocalCohomology.sectionMultiplication f ℱ)).hom ≫
      cokernel.map
        ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          (ModuleCech.LocalCohomology.sectionMultiplication f ℱ))
        (ModuleCech.LocalCohomology.sectionMultiplication
          (fun i ↦ g.appTop.hom (f i)) ((Scheme.Modules.pullback g).obj ℱ))
        (sectionSumPullback g ℱ) (coefficientPullback g ℱ)
        (sectionMultiplication_pullback g f ℱ) := sorry

/-- The canonical coefficient and quotient pullback maps commute with the two cokernel
projections. -/
theorem quotientProjectionCommSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    CommSq
      ((RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
        ((ModuleCech.LocalCohomology.quotientProjection f).app ℱ))
      (coefficientPullback g ℱ) (quotientPullback g f ℱ)
      ((ModuleCech.LocalCohomology.quotientProjection
        (fun i ↦ g.appTop.hom (f i))).app ((Scheme.Modules.pullback g).obj ℱ)) := sorry

end ModuleCech.BaseChange
