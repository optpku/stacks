/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.ValuativeCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.7.3: if `f : X ⟶ B` is proper and of finite presentation, then
the Hilbert functor `hilbert f` satisfies the existence part of the valuative
criterion. -/
@[stacks 0DM8] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.instExistence :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Proper f],
    SchemeOver.ValuativeCriterion.Existence
      (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert f))
