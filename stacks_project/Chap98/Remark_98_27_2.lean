module

public import stacks_project.Chap98.Remark_98_27_2_GRingStalks
public import stacks_project.Chap98.Situation_98_27_1_Contraction
import StacksCheckRecall

/-!
# Extra G-ring hypothesis for Artin contractions
-/

@[expose] public section

open AlgebraicGeometry

/- Remark 98.27.2: the desired Artin contraction is not claimed for every
Situation 98.27.1 `ContractionSituation`, because the local rings of `S` must
be G-rings. -/
@[stacks 0GH9] #check Scheme.HasGRingStalks

#check Scheme.HasGRingStalks.spec
#check Scheme.hasGRingStalks_iff_forall
#check Scheme.instHasGRingStalks_of_isGRing
