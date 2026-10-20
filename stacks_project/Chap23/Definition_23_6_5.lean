module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.OfPredifferential
import StacksCheckRecall

@[expose] public section

universe u v

variable (R : Type u) [CommRing R]

/- Definition 23.6.5 (09PJ): a nonnegative strictly graded-commutative chain DGA equipped with
divided powers on its positive even part, compatible with the chain differential. -/
@[stacks 09PJ]
#check (DividedPowerChainAlgebra.{u, v} R : Type (max u (v + 1)))

#check @ChainDGAlgebra.DividedPowers.IsCompatible
#check @ChainDGAlgebra.DividedPowers.isCompatible_iff
#check @DividedPowerChainAlgebra.gradedPredifferential
#check @DividedPowerChainAlgebra.gradedPredifferential_preservesDP
#check @DividedPowerChainAlgebra.toGradedPredifferential
#check @DividedPowerChainAlgebra.toGradedPredifferential_isSquareZero
#check @DividedPowerGradedAlgebra.Predifferential.toChainAlgebra
#check @DividedPowerGradedAlgebra.Predifferential.toChainAlgebra_toGradedAlgebra
#check @DividedPowerGradedAlgebra.Predifferential.toChainAlgebra_d_apply
#check @DividedPowerChainAlgebra.Hom
#check @DividedPowerChainAlgebra.toGraded
