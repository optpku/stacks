/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.ClosedImmersion

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.4.6: a closed immersion between algebraic spaces separated and
of finite presentation over `B` induces a closed immersion of coherent-sheaf
stacks by pushforward. -/
@[stacks 0DNB] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.instClosedImmersion_map :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y],
    AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ClosedImmersion
      (AlgebraicGeometry.AlgebraicSpace.CohStack.map π y))
