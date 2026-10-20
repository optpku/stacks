/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.Closed
import StacksCheckRecall

@[expose] public section

/-!
# Canonical dual of a locally strictly perfect complex

The concrete closed dual and its exact-pairing laws are maintained by the reusable monoidal API.
-/

/- Example 21.48.2: a locally strictly perfect complex `F` has canonical dual
`MonoidalClosed.dual F`; the maps `𝟙_ ⟶ F ⊗ MonoidalClosed.dual F` and
`MonoidalClosed.dual F ⊗ F ⟶ 𝟙_` form `ExactPairing F (MonoidalClosed.dual F)`. -/
@[stacks 0FPR]
#check @RingedSite.CochainComplex.IsLocallyStrictlyPerfect.rightExactPairing
#check @RingedSite.CochainComplex.IsLocallyStrictlyPerfect.rightExactPairing_nonempty
#check @RingedSite.CochainComplex.IsLocallyStrictlyPerfect.isRightDualizable

#check @CategoryTheory.MonoidalClosed.Dual.exactPairing_coevaluation
#check @CategoryTheory.MonoidalClosed.Dual.exactPairing_evaluation
