/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Invertible
import StacksCheckRecall

@[expose] public section

/- The source-facing local shifted-invertible owner and Lemma 21.49.2 (3) now live in ReasLib.
This historical path retains the same short checks for downstream discovery. -/
@[stacks 0FPY "local shifted-invertibility object property"]
#check @RingedSite.Hom.ModuleDerived.locallyShiftedInvertible

@[stacks 0FPY "local shifted-invertibility cover witness"]
#check @RingedSite.Hom.ModuleDerived.IsLocallyShiftedInvertible.exists_cover
