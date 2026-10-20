module

public import ReasLib.RingTheory.RegularLocalRing.Parameters.Jacobian
import StacksCheckRecall

/-!
# Lemma 15.48.3

@stack 0GEE

Lemma 15.48.3 is owned by the Jacobian criterion for partial regular systems of parameters.  The
two source conclusions retain the hypothesis `1 ≤ m`.
-/

@[expose] public section

/- @stack 0GEE -- Lemma 15.48.3 (1): regular quotient. -/
@[stacks 0GEE "Lemma 15.48.3 (1)"]
#check @IsRegularLocalRing.quotient_parameterIdeal_of_jacobianDet_isUnit

/- @stack 0GEE -- Lemma 15.48.3 (2): regular sequence. -/
@[stacks 0GEE "Lemma 15.48.3 (2)"]
#check @IsRegularLocalRing.sequence_isRegular_of_jacobianDet_isUnit

#check @IsLocalRing.IsPartOfRegularSystemOfParameters.of_jacobianDet_isUnit
