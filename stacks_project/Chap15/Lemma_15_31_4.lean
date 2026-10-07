module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity.BaseChange

/-!
# Lemma 15.31.4

@stack 0CEP
-/

@[expose] public section

/-! # Lemma 15.31.4: regularity under tensor base change -/

/- Lemma 15.31.4 (1), tag `0CEP`: a quasi-regular family with flat quotient remains
quasi-regular after arbitrary tensor base change. -/
@[stacks 0CEP "base change of a quasi-regular family with flat quotient"]
#check @RingTheory.Sequence.IsQuasiRegularSequence.baseChange_of_flat_quotient

/- Lemma 15.31.4 (2), tag `0CEP`: an `H₁`-regular family with flat quotient remains
`H₁`-regular after arbitrary tensor base change. -/
@[stacks 0CEP "base change of an H1-regular family with flat quotient"]
#check @RingTheory.Sequence.IsH1RegularSequence.baseChange_of_flat_quotient
