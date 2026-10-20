/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived.Exact
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open SheafOfModules.ClosedSubset

noncomputable section

universe u

namespace ModuleCech.BaseChange

/-- The canonical base-change map for restriction to an open subspace followed by direct image. -/
noncomputable def openSummandMap {X X' : Scheme.{u}} (g : X' ⟶ X)
    (U : Opens X) (ℱ : X.Modules) :
    (Scheme.Modules.pullback g).obj
        ((RingedSpace.modulePushforwardFromOpen U).obj
          ((RingedSpace.moduleRestrictionToOpen X.toRingedSpace U).obj ℱ)) ⟶
      (RingedSpace.modulePushforwardFromOpen
        (RingedSpace.preimageOpen g.toLRSHom.toShHom U)).obj
          ((RingedSpace.moduleRestrictionToOpen X'.toRingedSpace
            (RingedSpace.preimageOpen g.toLRSHom.toShHom U)).obj
              ((Scheme.Modules.pullback g).obj ℱ)) :=
  let sq : CommSq
      (RingedSpace.restrictedMorphismToOpen g.toLRSHom.toShHom U)
      (X'.toRingedSpace.ofRestrict
        (RingedSpace.preimageOpen g.toLRSHom.toShHom U).isOpenEmbedding)
      (X.toRingedSpace.ofRestrict U.isOpenEmbedding) g.toLRSHom.toShHom :=
    ⟨RingedSpace.restrictedMorphismToOpen_fac g.toLRSHom.toShHom U⟩
  (RingedSpace.Hom.BaseChange.map sq).app
      ((RingedSpace.moduleRestrictionToOpen X.toRingedSpace U).obj ℱ) ≫
    (RingedSpace.modulePushforwardFromOpen
      (RingedSpace.preimageOpen g.toLRSHom.toShHom U)).map
        ((RingedSpace.Hom.BaseChange.pullbackIso sq).inv.app ℱ)

/-- The open-summand base-change map is the mate for the canonical restricted-open square,
followed by the pullback-composition identification. -/
theorem openSummandMap_def {X X' : Scheme.{u}} (g : X' ⟶ X)
    (U : Opens X) (ℱ : X.Modules) :
    openSummandMap g U ℱ =
      let sq : CommSq
          (RingedSpace.restrictedMorphismToOpen g.toLRSHom.toShHom U)
          (X'.toRingedSpace.ofRestrict
            (RingedSpace.preimageOpen g.toLRSHom.toShHom U).isOpenEmbedding)
          (X.toRingedSpace.ofRestrict U.isOpenEmbedding) g.toLRSHom.toShHom :=
        ⟨RingedSpace.restrictedMorphismToOpen_fac g.toLRSHom.toShHom U⟩
      (RingedSpace.Hom.BaseChange.map sq).app
          ((RingedSpace.moduleRestrictionToOpen X.toRingedSpace U).obj ℱ) ≫
        (RingedSpace.modulePushforwardFromOpen
          (RingedSpace.preimageOpen g.toLRSHom.toShHom U)).map
            ((RingedSpace.Hom.BaseChange.pullbackIso sq).inv.app ℱ) := sorry

/-- Pullback carries the finite intersection belonging to an ordered principal-open Čech
summand to the corresponding intersection of the pulled-back principal opens. -/
theorem intersection_preimage {X X' : Scheme.{u}} (g : X' ⟶ X) {c p : ℕ}
    (f : Fin c → Γ(X, ⊤)) (σ : OrderedCechIndex (ULift.{u} (Fin c)) p) :
    RingedSpace.preimageOpen g.toLRSHom.toShHom
        (TopCat.Presheaf.Cech.intersection
          (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) σ.toFun) =
      TopCat.Presheaf.Cech.intersection
        (fun i : ULift.{u} (Fin c) ↦ X'.basicOpen (g.appTop.hom (f i.down))) σ.toFun := sorry

/-- The base-change map on one ordered principal-open Čech summand. -/
noncomputable def summandMap {X X' : Scheme.{u}} (g : X' ⟶ X) {c p : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (σ : OrderedCechIndex (ULift.{u} (Fin c)) p) :
    (Scheme.Modules.pullback g).obj
        (Scheme.ModuleCech.Ordered.summand
          (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) ℱ p σ) ⟶
      Scheme.ModuleCech.Ordered.summand
        (fun i : ULift.{u} (Fin c) ↦ X'.basicOpen (g.appTop.hom (f i.down)))
        ((Scheme.Modules.pullback g).obj ℱ) p σ :=
  openSummandMap g
      (TopCat.Presheaf.Cech.intersection
        (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) σ.toFun) ℱ ≫
    eqToHom (congrArg
      (fun U : Opens X' ↦
        (RingedSpace.modulePushforwardFromOpen U).obj
          ((RingedSpace.moduleRestrictionToOpen X'.toRingedSpace U).obj
            ((Scheme.Modules.pullback g).obj ℱ)))
      (intersection_preimage g f σ))

/-- The summand comparison is the open-subspace base-change map followed by transport along
the principal-open intersection equality. -/
theorem summandMap_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c p : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (σ : OrderedCechIndex (ULift.{u} (Fin c)) p) :
    summandMap g f ℱ σ =
      openSummandMap g
          (TopCat.Presheaf.Cech.intersection
            (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) σ.toFun) ℱ ≫
        eqToHom (congrArg
          (fun U : Opens X' ↦
            (RingedSpace.modulePushforwardFromOpen U).obj
              ((RingedSpace.moduleRestrictionToOpen X'.toRingedSpace U).obj
                ((Scheme.Modules.pullback g).obj ℱ)))
          (intersection_preimage g f σ)) := sorry

/-- The base-change map on a positive-degree ordered principal-open Čech term. -/
noncomputable def termMap {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (p : ℕ) :
    (Scheme.Modules.pullback g).obj
        (Scheme.ModuleCech.Ordered.term
          (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) ℱ p) ⟶
      Scheme.ModuleCech.Ordered.term
        (fun i : ULift.{u} (Fin c) ↦ X'.basicOpen (g.appTop.hom (f i.down)))
        ((Scheme.Modules.pullback g).obj ℱ) p :=
  biproduct.lift fun σ ↦
    (Scheme.Modules.pullback g).map
        (biproduct.π
          (fun τ : OrderedCechIndex (ULift.{u} (Fin c)) p ↦
            Scheme.ModuleCech.Ordered.summand
              (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) ℱ p τ) σ) ≫
      summandMap g f ℱ σ

/-- Projection to a target summand after `termMap` is the corresponding pulled-back projection
followed by the summand base-change map. -/
theorem termMap_π {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (p : ℕ)
    (σ : OrderedCechIndex (ULift.{u} (Fin c)) p) :
    termMap g f ℱ p ≫
        biproduct.π
          (fun τ : OrderedCechIndex (ULift.{u} (Fin c)) p ↦
            Scheme.ModuleCech.Ordered.summand
              (fun i : ULift.{u} (Fin c) ↦ X'.basicOpen (g.appTop.hom (f i.down)))
              ((Scheme.Modules.pullback g).obj ℱ) p τ) σ =
      (Scheme.Modules.pullback g).map
          (biproduct.π
            (fun τ : OrderedCechIndex (ULift.{u} (Fin c)) p ↦
              Scheme.ModuleCech.Ordered.summand
                (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) ℱ p τ) σ) ≫
        summandMap g f ℱ σ := sorry

/-- The degreewise comparison from termwise pullback of an extended principal-open Čech complex
to the extended Čech complex of the pulled-back equations and module. -/
noncomputable def component {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) : ∀ n,
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (ModuleCech.ofSections f ℱ)).X n ⟶
      (ModuleCech.ofSections (fun i ↦ g.appTop.hom (f i))
        ((Scheme.Modules.pullback g).obj ℱ)).X n
  | 0 => 𝟙 _
  | p + 1 => termMap g f ℱ p

/-- In degree zero, the Čech pullback comparison is the identity of the pulled-back
coefficient module. -/
theorem component_zero {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    component g f ℱ 0 = 𝟙 _ := sorry

/-- In degree `p + 1`, the Čech pullback comparison is `termMap`. -/
theorem component_succ {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (p : ℕ) :
    component g f ℱ (p + 1) = termMap g f ℱ p := sorry

/-- The degreewise Čech pullback comparisons commute with the differentials. -/
theorem component_comm {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    component g f ℱ i ≫
        (ModuleCech.ofSections (fun k ↦ g.appTop.hom (f k))
          ((Scheme.Modules.pullback g).obj ℱ)).d i j =
      ((((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (ModuleCech.ofSections f ℱ)).d i j) ≫ component g f ℱ j := sorry

/-- The concrete morphism from termwise pullback of an extended principal-open Čech complex to
the extended Čech complex of the pulled-back equations and coefficient module. -/
noncomputable def complexMap {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (ModuleCech.ofSections f ℱ) ⟶
      ModuleCech.ofSections (fun i ↦ g.appTop.hom (f i))
        ((Scheme.Modules.pullback g).obj ℱ) :=
  HomologicalComplex.Hom.mk (component g f ℱ) (component_comm g f ℱ)

/-- The degree-`n` component of `complexMap` is the explicit map `component`. -/
theorem complexMap_f {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (n : ℕ) :
    (complexMap g f ℱ).f n = component g f ℱ n := sorry

/-- The concrete Čech pullback map is natural in the coefficient module. -/
theorem complexMap_naturality {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (up ℕ)).map
          ((ModuleCech.ofSectionsFunctor f).map φ) ≫ complexMap g f 𝒢 =
      complexMap g f ℱ ≫
        (ModuleCech.ofSectionsFunctor (fun i ↦ g.appTop.hom (f i))).map
          ((Scheme.Modules.pullback g).map φ) := sorry

/-- The concrete Čech pullback map commutes with projection to the coefficient module in degree
zero. -/
theorem projectionCommSq {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    CommSq (complexMap g f ℱ)
      (((Scheme.Modules.pullback g).mapHomologicalComplex (up ℕ)).map
        ((ModuleCech.ofSectionsProjection f).app ℱ))
      ((ModuleCech.ofSectionsProjection (fun i ↦ g.appTop.hom (f i))).app
        ((Scheme.Modules.pullback g).obj ℱ))
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pullback g) (up ℕ) 0).hom.app ℱ) := sorry

/-- The canonical total-left-derived comparison from derived pullback of a principal-open Čech
complex to the derived realization of its termwise pullback. -/
noncomputable def derivedPullbackComparison {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).obj
        ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ) ⟶
      (ModuleCech.toRingedSpaceDerived X').obj
        (((Scheme.Modules.pullback g).mapHomologicalComplex (up ℕ)).obj
          (ModuleCech.ofSections f ℱ)) :=
  let K := ((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
    (ModuleCech.ofSections f ℱ)
  (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
      ((DerivedCategory.quotientCompQhIso X.toRingedSpace.Modules).inv.app
        (K.extend embeddingUpNat)) ≫
    ((RingedSpace.modulePullbackToDerived g.toLRSHom.toShHom).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
        ((HomotopyCategory.quotient X.toRingedSpace.Modules (up ℤ)).obj
          (K.extend embeddingUpNat)) ≫
    DerivedCategory.Q.map
      (ComplexShape.Embedding.mapAppIso embeddingUpNat
        (RingedSpace.Hom.pullback g.toLRSHom.toShHom) K).hom

/-- The derived-pullback comparison is the total-left-derived counit followed by the canonical
extension-by-zero/change-of-coefficients identification. -/
theorem derivedPullbackComparison_def {X X' : Scheme.{u}} (g : X' ⟶ X)
    {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    derivedPullbackComparison g f ℱ =
      let K := ((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
        (ModuleCech.ofSections f ℱ)
      (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).map
          ((DerivedCategory.quotientCompQhIso X.toRingedSpace.Modules).inv.app
            (K.extend embeddingUpNat)) ≫
        ((RingedSpace.modulePullbackToDerived g.toLRSHom.toShHom).totalLeftDerivedCounit
          DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app
            ((HomotopyCategory.quotient X.toRingedSpace.Modules (up ℤ)).obj
              (K.extend embeddingUpNat)) ≫
        DerivedCategory.Q.map
          (ComplexShape.Embedding.mapAppIso embeddingUpNat
            (RingedSpace.Hom.pullback g.toLRSHom.toShHom) K).hom := sorry

/-- The canonical map from derived pullback of the extended Čech complex to the extended Čech
complex formed from the pulled-back equations and module. -/
noncomputable def derivedMap {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).obj
        ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ) ⟶
      (ModuleCech.ofSectionsDerivedFunctor (fun i ↦ g.appTop.hom (f i))).obj
        ((Scheme.Modules.pullback g).obj ℱ) :=
  derivedPullbackComparison g f ℱ ≫
    (ModuleCech.toRingedSpaceDerived X').map (complexMap g f ℱ)

/-- The derived Čech map factors through the total-left-derived counit and the localized
termwise Čech comparison. -/
theorem derivedMap_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    derivedMap g f ℱ = derivedPullbackComparison g f ℱ ≫
      (ModuleCech.toRingedSpaceDerived X').map (complexMap g f ℱ) := sorry

/-- The map on degree-`n` Čech cohomology induced by the concrete termwise pullback map. -/
noncomputable def cohomologyMap {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (n : ℕ) :
    ((((Scheme.Modules.pullback g).mapHomologicalComplex (up ℕ)).obj
        (ModuleCech.ofSections f ℱ)).homology n) ⟶
      (ModuleCech.ofSections (fun i ↦ g.appTop.hom (f i))
        ((Scheme.Modules.pullback g).obj ℱ)).homology n :=
  (HomologicalComplex.homologyFunctor X'.Modules (up ℕ) n).map
    (complexMap g f ℱ)

/-- `cohomologyMap` is obtained by applying the homology functor to `complexMap`. -/
theorem cohomologyMap_def {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (n : ℕ) :
    cohomologyMap g f ℱ n =
      (HomologicalComplex.homologyFunctor X'.Modules (up ℕ) n).map
        (complexMap g f ℱ) := sorry

/-- Pulling back the ideal generated by a finite family of global functions gives the ideal
generated by their pullbacks. Together with `Scheme.ClosedSubschemeStructure.comapIso`, this identifies
the pulled-back zero subscheme with the scheme-theoretic pullback. -/
theorem ideal_comap {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range f))).comap g =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range fun i ↦ g.appTop.hom (f i))) := sorry

/-- The common zero locus of the pulled-back equations is the inverse image of the original
common zero locus. -/
theorem zeroLocus_preimage {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) :
    RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom
        (ModuleCech.ofSectionsZeroLocus f) =
      ModuleCech.ofSectionsZeroLocus (fun i ↦ g.appTop.hom (f i)) := sorry


end ModuleCech.BaseChange

