/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.ProperSupport
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap76.«76_42_2_1_Completion»

/-! Compatibility check for coherent completion with proper support intersection. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

#check (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.homMap_bijective :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)],
    ∀ (ℱ 𝒢 : Coh X),
      ClosedSubset.ProperOver (SchemeRealization.toBase X)
        (closedSupport ℱ.obj ⊓ closedSupport 𝒢.obj) →
      Function.Bijective (fun f : ℱ ⟶ 𝒢 ↦
        (CoherentCompletion.functor (pullbackIdeal I (SchemeRealization.toBase X))).map f))
