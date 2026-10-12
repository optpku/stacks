/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Leray.Degeneration
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.14.6

The two standard degeneration criteria are shared by `RingedSite.Hom.Leray.Degeneration`.
They use `moduleGlobalCohomology` and `higherDirectImageModule`, so the chapter entry needs no
local cohomology wrapper or higher-direct-image notation.
-/

/- Lemma 21.14.6 (1) (0733): vanishing positive higher direct images gives the single-row
Leray degeneration comparing source cohomology with cohomology of the ordinary direct image. -/
@[stacks 0733 "(1)"] #check @RingedSite.Hom.Leray.Degeneration.row

#check @RingedSite.Hom.HigherDirectImage.vanishesAboveZero_iff

/- Lemma 21.14.6 (2) (0733): target-acyclic higher direct images give the single-column Leray
degeneration comparing source cohomology with degree-zero cohomology of the higher direct image. -/
@[stacks 0733 "(2)"] #check @RingedSite.Hom.Leray.Degeneration.column

end
