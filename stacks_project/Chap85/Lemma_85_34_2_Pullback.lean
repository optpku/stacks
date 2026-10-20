/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Descent
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_34_1_Comparison

/-! # Module functors and quasi-coherent restrictions of a spaces-étale augmentation -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.modulePullback :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X),
    RingedSite.ModuleCat.{u} (spacesRingedSite X) ⥤
      RingedSite.ModuleCat.{u} (etaleTotalRingedSite U))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.modulePushforward :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X),
    RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) ⥤
      RingedSite.ModuleCat.{u} (spacesRingedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.moduleAdjunction :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X), modulePullback a ⊣ modulePushforward a)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.pullback :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X),
    (spacesQuasiCoherentModuleProperty X).FullSubcategory ⥤ QCoh U)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.pushforward :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
    QCoh U ⥤ (spacesQuasiCoherentModuleProperty X).FullSubcategory)

