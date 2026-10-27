/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraicity
import StacksCheckRecall

/-!
# Theorem 99.6.1

If `f : X ⟶ B` is a finitely presented separated morphism of algebraic spaces
over a scheme `S`, then `CohStack f` is an algebraic stack over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Theorem 99.6.1 (Algebraicity of the stack of coherent sheaves; general case)
For a finitely presented separated morphism of algebraic spaces over a scheme,
the groupoid fibration of coherent sheaves is an algebraic stack. -/
@[stacks 09DS] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.instAlgebraicStackOfSeparated :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [FinitePresentation f] → [Separated f] →
        AlgebraicGeometry.AlgebraicSpace.CohStack.AlgebraicStack
          (AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoids f))
