/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

/-! # Derived pullback-pushforward adjunction on algebraic spaces

The unbounded derived adjunction retains the established source-facing functor spellings.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/-- Unbounded derived module pullback is left adjoint to derived module pushforward. -/
noncomputable def AlgebraicGeometry.AlgebraicSpace.modulePullbackDerivedPushforwardAdjunction
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    modulePullbackDerived f ⊣ Modules.pushforwardDerived f :=
  Modules.derivedPullbackPushforwardAdjunction f

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerivedPushforwardAdjunction :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X),
    modulePullbackDerived f ⊣ Modules.pushforwardDerived f)
