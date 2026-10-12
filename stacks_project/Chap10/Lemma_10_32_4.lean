/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent.Unit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.32.4

@stack 0AMG

Units are detected after quotienting by a locally nilpotent ideal.
-/

@[stacks 0AMG "units modulo a locally nilpotent ideal"]
#check @Ideal.IsLocallyNilpotent.isUnit_iff_quotient_mk
