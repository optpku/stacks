/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic.Flat
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/- Theorem 99.5.12 (Algebraicity of the stack of coherent sheaves; flat case)
The stack of coherent sheaves for a finitely presented, separated, flat morphism
of algebraic spaces over a scheme is algebraic.
-/
@[stacks 08WC] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.instAlgebraicStackOfFlat :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] [Separated f] [Flat f], AlgebraicStack (toGroupoids f))

end AlgebraicGeometry.AlgebraicSpace.CohStack
