/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.KInjective

/-!
# Lemma 15.56.2

@stack 0916
-/

@[expose] public section

/- Lemma 15.56.2 (0916): restriction of scalars along a ring epimorphism reflects
K-injectivity. -/
@[stacks 0916]
#check @ModuleCat.RestrictScalars.isKInjective_of_epi

#check @RingHom.full_of_epi
#check @ModuleCat.restrictCoextendScalarsAdj
