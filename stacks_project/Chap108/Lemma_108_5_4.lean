/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Pushforward
public import stacks_project.Chap108.Lemma_108_5_4_Map

/-!
# Affine quasi-finite pushforward on the Grothendieck Quot functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.5.4: affine quasi-finite pushforward induces a morphism of the
proper-support Quot functors for separated, finitely presented algebraic spaces. -/
@[stacks 0DP1] #check (AlgebraicGeometry.AlgebraicSpace.Quot.map :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    (F : X.Modules) [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent],
    Quot.quot (π ≫ y) F ⟶ Quot.quot y ((Modules.pushforward π).obj F))
