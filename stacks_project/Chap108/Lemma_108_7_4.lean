/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.OpenImmersion

/-!
# Lemma 108.7.4

An open immersion of separated finite-presentation algebraic spaces over `B`
induces an open immersion of Hilbert functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 108.7.4: An open immersion of algebraic spaces separated and of finite
presentation over `B` induces an open immersion of their Hilbert functors. -/
@[stacks 0DPE] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.isOpenImmersion_map :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (π : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y],
    Hilbert.IsOpenImmersionOnSchemesOver (Hilbert.map π y))
