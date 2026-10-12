/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GlobalDimension.RegularLocal
import StacksCheckRecall

/-!
# Regular Local Rings and Finite Global Dimension

@stack 0AFS
-/

@[expose] public section

/- Lemma 10.110.6 (1) (Stacks tag `0AFS`): a Noetherian local ring is regular
local if and only if it has finite global dimension. -/
@[stacks 0AFS "(1)"]
#check @IsRegularLocalRing.iff_isFiniteGlobalDimensionRing

/- Lemma 10.110.6 (2) (Stacks tag `0AFS`): under these equivalent conditions,
the localization at every prime is regular local. -/
@[stacks 0AFS "(2)"]
#check @IsRegularLocalRing.localizationAtPrime

/- The canonical global-regularity instance packages clause (2). -/
#check @IsRegularRing.instOfIsRegularLocalRing
