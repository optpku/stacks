module

public import ReasLib.RingTheory.Etale.LocallyNilpotent
public import ReasLib.RingTheory.Henselian.LocallyNilpotent
import StacksCheckRecall

/-!
# Locally nilpotent quotients and henselian pairs

Lemma 15.11.2 is split between the categorical etale-reduction owner and the independent
henselian-pair consequence for a locally nilpotent ideal.

@stack 0ALI
-/

@[expose] public section

@[stacks 0ALI "category of etale algebras"]
#check @CommAlgCat.Etale

@[stacks 0ALI "base change of etale algebras"]
#check @CommAlgCat.Etale.baseChange

@[stacks 0ALI "reduction of etale algebras"]
#check @CommAlgCat.Etale.reduction

@[stacks 0ALI "etale equivalence over a locally nilpotent quotient"]
#check @CommAlgCat.Etale.reduction_isEquivalence_of_isLocallyNilpotent

@[stacks 0ALI "locally nilpotent ideals are henselian"]
#check @Ideal.IsLocallyNilpotent.henselianRing
