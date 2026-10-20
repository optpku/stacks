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
# Dualizable complexes are locally strictly perfect

The geometric criterion and uniqueness of a chosen dual are maintained by independent reusable
owners.
-/

/- Lemma 21.48.3: if `p : ExactPairing F G`, then `F` is locally strictly perfect and the
chosen dual `G` is canonically isomorphic to `MonoidalClosed.dual F`. -/
@[stacks 0FPS]
#check @RingedSite.CochainComplex.IsLocallyStrictlyPerfect.ofExactPairing

#check @RingedSite.CochainComplex.isLocallyStrictlyPerfect_of_isRightDualizable
#check @CategoryTheory.MonoidalClosed.Dual.rightDualIso
