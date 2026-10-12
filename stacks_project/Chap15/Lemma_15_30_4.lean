/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity

/-!
# Multiplying the last member of a Koszul-regular family

@stack 062G
-/

@[expose] public section

/- Lemma 15.30.4 (1): `M`-`H₁`-regularity is preserved when two possible last entries are
multiplied. -/
@[stacks 062G "Lemma 15.30.4 (1)"]
#check @RingTheory.Sequence.IsH1RegularOn.snoc_mul

/- Lemma 15.30.4 (2): `M`-Koszul-regularity is preserved when two possible last entries are
multiplied. -/
@[stacks 062G "Lemma 15.30.4 (2)"]
#check @RingTheory.Sequence.IsKoszulRegularOn.snoc_mul
