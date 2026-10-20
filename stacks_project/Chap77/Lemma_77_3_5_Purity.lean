/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap67.Lemma_67_13_4
public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap67.Lemma_67_45_9
public import stacks_project.Chap67.Lemma_67_45_10
public import stacks_project.Chap68.Lemma_68_17_2
public import stacks_project.Chap68.Lemma_68_17_6
public import stacks_project.Chap74.Lemma_74_6_6
public import stacks_project.Chap77.Lemma_77_3_2_Purity

/-!
# Purity of pushforwards along closed immersions

In Situation 77.2.1, a finite type quasi-coherent module on a closed subspace is
(universally) pure above a point if and only if its pushforward is.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A finite type quasi-coherent module on a closed subspace is pure above a
point of the base if and only if its pushforward is pure above that point. -/
theorem isPureAlong_pushforward_iff_of_isClosedImmersion
    {Z : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] [Decent f]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] (y : Points Y) :
    G.IsPureAlong (i ≫ f) y ↔ ((pushforward i).obj G).IsPureAlong f y :=
  sorry

/-- A finite type quasi-coherent module on a closed subspace is universally
pure above a point of the base if and only if its pushforward is universally
pure above that point. -/
theorem isUniversallyPureAlong_pushforward_iff_of_isClosedImmersion
    {Z : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] [Decent f]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] (y : Points Y) :
    G.IsUniversallyPureAlong (i ≫ f) y ↔
      ((pushforward i).obj G).IsUniversallyPureAlong f y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
