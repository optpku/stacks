/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Regularity
import StacksCheckRecall

/-!
# Lemma 15.38.2

@stack 07EI
-/

@[expose] public section

/- Lemma 15.38.2, tag `07EI`: maximal-ideal-adic formal smoothness of a Noetherian local
algebra over a field implies that the local ring is regular. -/
@[stacks 07EI]
#check @isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic
