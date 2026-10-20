/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.InfiniteAffineCounterexample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Example 29.3.4: over a field, the explicit closed subscheme of the punctured spectrum of
the polynomial ring in countably many variables is an immersion into the ambient spectrum,
but it does not factor as an open immersion followed by a closed immersion. -/
@[stacks 01QW] #check
  (AlgebraicGeometry.InfiniteAffineCounterexample.immersion_spec :
    ∀ (k : Type u) [Field k],
      IsImmersion (AlgebraicGeometry.InfiniteAffineCounterexample.immersion k) ∧
        ¬ IsOpenThenClosed (AlgebraicGeometry.InfiniteAffineCounterexample.immersion k))
