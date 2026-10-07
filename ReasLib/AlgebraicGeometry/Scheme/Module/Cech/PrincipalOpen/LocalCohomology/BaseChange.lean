module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.BaseChange.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology

@[expose] public section

/-!
# Principal-open Čech and local-cohomology base change

This module compares pullback of an extended principal-open Čech complex with pullback of the
corresponding derived object with support, including the upper cohomology and class maps.
-/

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
