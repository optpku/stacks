/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.QuasiRegular.Deformation

/-!
# Lemma 15.31.5

@stack 0CEQ
-/

@[expose] public section

/-! # Lemma 15.31.5: flat quasi-regular quotients across a thickening -/

/- Lemma 15.31.5, tag `0CEQ`: flatness of a quotient by a finite quasi-regular family deforms
across a locally nilpotent ideal of the base. -/
@[stacks 0CEQ "flat quasi-regular quotients across locally nilpotent thickenings"]
#check @RingTheory.Sequence.IsQuasiRegularSequence.flatQuotient_of_locallyNilpotent
