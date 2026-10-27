/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.ValuativeCriterion
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

/- Lemma 108.8.3: in the flat, proper, finitely presented setup, smoothness
implies valuative existence for the Picard structure morphism. -/
@[stacks 0DNG] #check (AlgebraicGeometry.AlgebraicSpace.Picard.toBase.existence :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    [Flat f] → [FinitePresentation f] → [Proper f] → [Smooth f] →
      CohStack.Hom.ValuativeCriterion.Existence (Picard.toBase f))
