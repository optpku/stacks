module

public import ReasLib.CategoryTheory.Abelian.CommSq
import StacksCheckRecall

@[expose] public section

/-! Lemma 12.5.13 is the abelian pullback/pushout comparison API. -/

@[stacks 08N4] #check @CategoryTheory.isPushout_of_isPullback_of_epi_right
@[stacks 08N4] #check @CategoryTheory.epi_left_of_isPullback_of_epi_right
@[stacks 08N4] #check @CategoryTheory.isPullback_of_isPushout_of_mono_top
@[stacks 08N4] #check @CategoryTheory.mono_bottom_of_isPushout_of_mono_top

end
