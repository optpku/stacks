/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Pushforward

/-!
# Quasi-finite pushforward of coherent sheaves

A quasi-finite morphism of separated finite-presentation algebraic spaces over
`B` induces a morphism of groupoid fibrations of coherent sheaves.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack

universe u

/- Lemma 108.4.4: fibrewise pushforward induces a morphism of coherent-sheaf
stacks for a quasi-finite morphism between separated finite-presentation
algebraic spaces over `B`. -/
@[stacks 0DN9] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.map :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y],
    toGroupoids (π ≫ y) ⟶ toGroupoids y)
