/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Support
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Topology

universe u

/- Lemma 59.71.7 (1): the surjective geometric-stalk locus of a constructible étale sheaf
morphism is constructible on a quasi-compact quasi-separated scheme. -/
@[stacks 09YS] #check (CategoryTheory.Sheaf.isConstructible_surjectiveStalkLocus :
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (hF : CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G) F)
    (hG : CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G) G),
    Topology.IsConstructible (CategoryTheory.Sheaf.surjectiveStalkLocus φ))

/- Lemma 59.71.7 (2): the injective geometric-stalk locus of a constructible étale sheaf
morphism is constructible on a quasi-compact quasi-separated scheme. -/
@[stacks 09YS] #check (CategoryTheory.Sheaf.isConstructible_injectiveStalkLocus :
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (hF : CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G) F)
    (hG : CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G) G),
    Topology.IsConstructible (CategoryTheory.Sheaf.injectiveStalkLocus φ))

/- Lemma 59.71.7 (3): the prescribed-map geometric-stalk locus of a constructible étale sheaf
morphism is constructible on a quasi-compact quasi-separated scheme. -/
@[stacks 09YS] #check (CategoryTheory.Sheaf.isConstructible_isoToMapStalkLocus :
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    {A B : Type (u + 1)} (f : A → B)
    (hF : CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G) F)
    (hG : CategoryTheory.Sheaf.IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G) G),
    Topology.IsConstructible (CategoryTheory.Sheaf.isoToMapStalkLocus φ f))

/- Lemma 59.71.7 (4): the support of a constructible abelian étale sheaf is constructible on a
quasi-compact quasi-separated scheme. -/
@[stacks 09YS] #check (CategoryTheory.Sheaf.isConstructible_abelianSheafSupport :
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp G) F),
    Topology.IsConstructible (CategoryTheory.Sheaf.abelianSheafSupport F))

/- Lemma 59.71.7 (5): the support of a constructible sheaf of modules over a Noetherian ring is
constructible on a quasi-compact quasi-separated scheme. -/
@[stacks 09YS] #check (CategoryTheory.Sheaf.isConstructible_moduleSheafSupport :
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : CategoryTheory.Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ↦
        CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule G) F),
    Topology.IsConstructible (CategoryTheory.Sheaf.moduleSheafSupport F))
