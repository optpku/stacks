/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Pi
import StacksCheckRecall

/-!
@stack 05D0
-/

@[expose] public section

/- Chap10 Lemma 10 91 3: an arbitrary power of a Noetherian commutative ring is flat and
Mittag-Leffler over that ring. -/
@[stacks 05D0]
#check @Module.noetherian_pi_flat_and_mittagLeffler

@[stacks 05D0 "Noetherian product flatness"]
#check @IsCoherentRing.piFlat

@[stacks 05D0 "product Mittag-Leffler criterion"]
#check @Module.MittagLeffler.piSelf
