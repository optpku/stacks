/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Stability

@[expose] public section

/-!
# Lemma 10.136.9

This chapter entry is a source-facing recall of the neutral stability API for
relative global complete intersections.

@stack 00SS
-/

/- Lemma 10.136.9 (00SS): relative global complete intersections are stable
under base change, localization away from an element, and passage across a
base localization. -/
#check @Algebra.Presentation.IsRelativeGlobalCompleteIntersection.baseChange
#check @Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv

/- Lemma 10.136.9 (1), tag `00SS`: relative global complete intersections are
stable under arbitrary base change. -/
@[stacks 00SS "relative global complete intersections are stable under base change"]
#check @Algebra.IsRelativeGlobalCompleteIntersection.baseChange

/- Lemma 10.136.9 (2), tag `00SS`: localization away from an element preserves
relative global complete intersections. -/
@[stacks 00SS "relative global complete intersections are stable under localization"]
#check @Algebra.IsRelativeGlobalCompleteIntersection.localizationAway

/- Lemma 10.136.9 (3), tag `00SS`: a base localization through which the
algebra map factors preserves the relative global complete-intersection property. -/
@[stacks 00SS "relative global complete intersections descend across a localization"]
#check @Algebra.IsRelativeGlobalCompleteIntersection.of_isLocalizationAway
