/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.RegularSequence
public import ReasLib.RingTheory.KrullDimension.RegularSequence
import StacksCheckRecall

/-!
# Lemma 10.104.2

@stack 02JN
-/

@[expose] public section

/- Lemma 10.104.2 (1) (Stacks tag `02JN`): regularity is equivalent to the
expected dimension of the quotient. -/
@[stacks 02JN]
#check @Module.CohenMacaulay.isRegular_iff_ringKrullDim_quotient_add_length_eq

/- Lemma 10.104.2 (2): a regular sequence in a Cohen--Macaulay local ring
extends to one whose length is the Krull dimension of the ring. -/
@[stacks 02JN "maximal regular-sequence extension"]
#check @RingTheory.Sequence.IsRegular.exists_extension_of_cohenMacaulay

/- Lemma 10.104.2 (3) (Stacks tag `02JN`): each quotient by a regular prefix
is Cohen--Macaulay. -/
@[stacks 02JN "Cohen-Macaulay prefix quotients"]
#check @RingTheory.Sequence.IsRegular.cohenMacaulay_quotient_take

/- Lemma 10.104.2 (4) (Stacks tag `02JN`): the quotient by the first `i`
elements has dimension `ringKrullDim R - i`. -/
@[stacks 02JN "regular-sequence prefix dimension"]
#check @RingTheory.Sequence.IsRegular.ringKrullDim_quotient_take_add_eq
