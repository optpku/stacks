/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent.Noetherian
import Mathlib.RingTheory.Noetherian.Nilpotent
import StacksCheckRecall

/-!
# Locally nilpotent ideals in Noetherian rings

@stack 00IM
-/

@[expose] public section

@[stacks 00IM "(1), finitely-generated radical-power bound"]
#check @Ideal.exists_pow_le_of_le_radical_of_fg

@[stacks 00IM "(2), locally nilpotent ideals are nilpotent"]
#check @Ideal.IsLocallyNilpotent.isNilpotent

@[stacks 00IM "(2), canonical Noetherian criterion"]
#check @Ideal.isLocallyNilpotent_iff_isNilpotent
