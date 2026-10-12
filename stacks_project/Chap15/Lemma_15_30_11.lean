/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity

/-!
# Lemma 15.30.11

@stack 0668
-/

@[expose] public section

/-! # Lemma 15.30.11: concatenating `H₁`-regular families -/

/- Lemma 15.30.11, tag `0668`: an `H₁`-regular family followed by an `H₁`-regular family
in its quotient ring is again `H₁`-regular. -/
@[stacks 0668 "concatenating H1-regular families across a quotient"]
#check @RingTheory.Sequence.IsH1RegularSequence.append_of_quotient
