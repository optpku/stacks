module

public import ReasLib.RingTheory.FittingIdeal.Presentation
import StacksCheckRecall

/-!
# Lemma 15.8.2

The source statement is the presentation-level Fitting ideal and its independence from a chosen
surjective finite free presentation.

@stack 07Z8
-/

@[expose] public section

/- The presentation-level Fitting-ideal owner is `presentationFittingIdeal`. -/
@[stacks 07Z8 "presentation Fitting ideals"]
#check @presentationFittingIdeal

/- Lemma 15.8.2: the presentation-level Fitting ideal is independent of the chosen surjective
finite free presentation. -/
@[stacks 07Z8 "presentation independence"]
#check @presentationFittingIdeal_eq_of_surjective
