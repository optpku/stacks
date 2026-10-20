/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.5.6: An open immersion between algebraic spaces separated and of
finite presentation over `B` induces an open immersion of Quot functors for
any quasi-coherent module `G` on the target and its pullback to the source. -/
@[stacks 0DP3] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.isOpenImmersion_openMap :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (j : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion j]
      [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
      [Separated y] [FinitePresentation y] (G : Y.Modules) [G.IsQuasicoherent],
      AlgebraicGeometry.AlgebraicSpace.Quot.IsOpenImmersionOnSchemesOver
        (AlgebraicGeometry.AlgebraicSpace.Quot.openMap j y G))
