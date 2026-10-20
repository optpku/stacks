/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Decent
import StacksCheckRecall

/- Example 68.6.2: the algebraic space 𝔸¹_ℚ / ℤ is not decent. -/
@[stacks 03ID] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.not_isDecent :
    ¬ AlgebraicGeometry.AlgebraicSpace.IsDecent
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.space ℚ))

/- Example 68.6.2: its generic point cannot be represented by a monomorphism from the
spectrum of a field. -/
@[stacks 03ID] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.not_existsMono_genericPoint :
    ¬ AlgebraicGeometry.AlgebraicSpace.existsMonoFieldValuedPoint
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.space ℚ)
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.genericSpacePoint ℚ))
