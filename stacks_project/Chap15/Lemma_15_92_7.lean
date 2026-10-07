module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Nakayama
import StacksCheckRecall

/-!
# Lemma 15.92.7: derived-complete Nakayama vanishing

@stack 09B9

The finite-generation quotient criterion is owned by ReasLib.  This file keeps the Stacks label and
the source-facing recall while avoiding a second list-of-generators implementation in Chap15.
-/

@[expose] public section

/- Lemma 15.92.7 (Stacks `09B9`): if `M / I M = 0` for a finitely generated `I` and `M` is derived
complete, then `M = 0`. -/
@[stacks 09B9 "derived-complete Nakayama vanishing"]
#check @ModuleCat.DerivedComplete.quotient_isZero

end
