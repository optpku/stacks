/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 67.42.1: If `f : X ⟶ Y` is a quasi-compact morphism of algebraic spaces
over a scheme `S` and `f` satisfies the existence part of the valuative criterion,
then `f` is universally closed. -/
@[stacks 03KA] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.of_quasiCompact_of_existence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
      [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f] →
      [AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence f] →
      AlgebraicGeometry.AlgebraicSpace.UniversallyClosed f)
