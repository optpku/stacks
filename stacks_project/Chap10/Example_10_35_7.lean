/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Jacobson.Product
import StacksCheckRecall

/-!
# Example 10.35.7

@stack 02CC

The reusable owner separates the away-localization Jacobson criterion from its application to an
infinite product of fields.
-/

/- Generic criterion used in Example 10.35.7: surjectivity of every canonical away-localization
map forces the source ring to be Jacobson. -/
@[stacks 02CC "away-localization criterion"]
#check @IsJacobsonRing.of_away_algebraMap_surjective

/- Example 10.35.7: an infinite product of fields is a Jacobson ring. -/
@[stacks 02CC "infinite product of fields"]
#check @Pi.instIsJacobsonRingOfInfinite
