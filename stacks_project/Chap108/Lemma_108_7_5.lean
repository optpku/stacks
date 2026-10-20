/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.ClosedImmersion

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.7.5: A closed immersion of separated finite-presentation algebraic
spaces over `B` induces a closed immersion of Hilbert functors. -/
@[stacks 0DPF] #check
  (AlgebraicGeometry.AlgebraicSpace.Hilbert.isClosedImmersion_map :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
      [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
      [Separated y] [FinitePresentation y],
      SchemeOver.IsClosedImmersion (Hilbert.closedMap π y))
