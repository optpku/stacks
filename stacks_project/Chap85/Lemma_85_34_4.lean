/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.DerivedDescent

/-! # Quasi-coherent unbounded descent for an fppf hypercovering -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

universe u

/- Lemma 85.34.4 (1): For an fppf hypercovering augmentation, quasi-coherent modules
on the total étale ringed topos form a weak Serre subcategory of all native module sheaves. -/
@[stacks 0DHF] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived.quasiCoherent_isWeakSerreClass :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X),
      IsFppfHypercovering a → (quasiCoherentModuleProperty U).IsWeakSerreClass)

/- Lemma 85.34.4 (2): Exact inverse image for the Section 85.32 total augmentation
is an equivalence on unbounded derived categories with quasi-coherent homology.
Its right adjoint is the canonical unbounded derived direct image Ra_* below. -/
@[stacks 0DHF] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived.pullback_isEquivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
      (QCohDerived.pullback a ha).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived.adjunction :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
    QCohDerived.pullback a ha ⊣ QCohDerived.pushforward a ha)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived.pushforward_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
    (E : QCohDerived.Total U),
    ((QCohDerived.pushforward a ha).obj E).obj = (EtaleModuleDerived.pushforward a).obj E.obj)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived.unit_app_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
    (E : QCohDerived.Base X), IsIso ((QCohDerived.ambientAdjunction a ha).unit.app E.obj))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived.counit_app_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
    (E : QCohDerived.Total U), IsIso ((QCohDerived.ambientAdjunction a ha).counit.app E.obj))
