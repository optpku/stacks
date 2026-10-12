/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.StandardSmooth
public import ReasLib.RingTheory.Smooth.Localization

@[expose] public section

/-!
# Standard Smooth Algebras

This source item is a canonical recall of the standard-smooth API.  The
generic localization and relative-global-complete-intersection statements are
owned by Mathlib and ReasLib rather than by this chapter.

@stack 00T7
-/

/- Lemma 10.137.6 (1), tag `00T7`: a standard smooth ring homomorphism is
smooth. -/
@[stacks 00T7 "standard smooth algebras are smooth"]
#check @RingHom.IsStandardSmooth.smooth

/- Lemma 10.137.6 (2), tag `00T7`: standard smoothness is preserved by target
away-localization. -/
@[stacks 00T7 "standard smoothness under target localization"]
#check @Algebra.IsStandardSmooth.localizationAway

/- Lemma 10.137.6 (3), tag `00T7`: standard smoothness is stable under base
change. -/
@[stacks 00T7 "standard smoothness under base change"]
#check @Algebra.IsStandardSmooth.baseChange

/- Lemma 10.137.6 (4), tag `00T7`: standard smoothness is preserved after
localizing the base away from an element that becomes a unit. -/
@[stacks 00T7 "standard smoothness under source localization"]
#check @Algebra.IsStandardSmooth.of_isUnit_base

/- Lemma 10.137.6 (5), tag `00T7`: a standard smooth algebra is a relative
global complete intersection. -/
@[stacks 00T7 "standard smooth is relative global complete intersection"]
#check @Algebra.IsStandardSmooth.isRelativeGlobalCompleteIntersection
