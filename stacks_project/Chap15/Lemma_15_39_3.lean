module

public import ReasLib.RingTheory.Completion.PowerSeriesPresentation
import StacksCheckRecall

/-!
# Lemma 15.39.3

@stack 07NN
-/

@[expose] public section

/- Lemma 15.39.3, tag `07NN`: a local map of Noetherian complete local rings has compatible
surjective power series presentations, with regular parameters, a flat comparison map, and
regular closed fiber. -/
@[stacks 07NN]
#check @exists_powerSeries_presentation_of_localHom_completeLocal
