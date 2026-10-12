/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.QuasiRegular.Deformation

/-!
# Lemma 15.31.6

@stack 0CER
-/

@[expose] public section

/-! # Lemma 15.31.6: smooth quasi-regular quotients across a thickening -/

/- Lemma 15.31.6, tag `0CER`: smoothness of a quotient by a finite quasi-regular family deforms
across a locally nilpotent ideal of the base. -/
@[stacks 0CER "smooth quasi-regular quotients across locally nilpotent thickenings"]
#check @RingTheory.Sequence.IsQuasiRegularSequence.smoothQuotient_of_locallyNilpotent
