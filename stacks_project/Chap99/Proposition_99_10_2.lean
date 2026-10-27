/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Algebraic
import StacksCheckRecall

/-!
# Proposition 99.10.2

If `f : X ⟶ B` is a flat, finitely presented, proper morphism of algebraic
spaces over a scheme `S`, then the Picard stack `Pic_{X/B}` is an algebraic
stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Proposition 99.10.2: the Picard stack of a flat, finitely presented, proper
morphism of algebraic spaces over a scheme is an algebraic stack. -/
@[stacks 0D04] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.instAlgebraicStack :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [Flat f] → [FinitePresentation f] → [Proper f] →
        CohStack.AlgebraicStack (Picard.toGroupoids f))

