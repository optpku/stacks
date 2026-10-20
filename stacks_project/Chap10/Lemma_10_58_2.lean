module

public import ReasLib.RingTheory.GradedAlgebra.FiniteType
import StacksCheckRecall

/-!
# Lemma 10.58.2

@stack 00JW
-/

@[stacks 00JW "finite-type criterion"]
#check @HomogeneousIdeal.finiteType_iff_irrelevant_fg

@[stacks 00JW "Noetherian criterion"]
#check @HomogeneousIdeal.isNoetherianRing_iff_degreeZero_and_irrelevant_fg

@[stacks 00JW "explicit Noetherian-to-finite-type bridge"]
#check @GradedAlgebra.finiteType_of_isNoetherian
