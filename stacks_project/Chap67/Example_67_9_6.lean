/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.UniversallyClosed
import StacksCheckRecall

@[expose] public section

universe u

/- Example 67.9.6: for a characteristic-zero field `k`, the structure morphism
`p : 𝔸¹_k / ℤ ⟶ Spec(k)` of the algebraic space from Spaces, Example 65.14.8 is
universally closed. -/
@[stacks 03IV] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.instUniversallyClosed_toBase :
    ∀ (k : Type u) [Field k] [CharZero k],
      AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase
          (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.space k)))
