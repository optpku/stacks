module

public import ReasLib.RingTheory.RegularLocalRing.Parameters.Dimension
import StacksCheckRecall

@[expose] public section

/-!
# Dimension after quotienting by parameters

Lemma 10.60.14, tag `02IE`, is owned by the reusable API for systems of
parameters in Noetherian local rings.  The regular-local specializations live
in `ReasLib.RingTheory.RegularLocalRing.Parameters.Properties`.

@stack 02IE
-/

/- Lemma 10.60.14 (1), tag `02IE`: quotienting a system of parameters by an
initial parameter ideal lowers Krull dimension by the prefix length. -/
@[stacks 02IE "(1)"]
#check @IsLocalRing.IsSystemOfParameters.ringKrullDim_quotient_parameterIdeal_eq_sub

/- Lemma 10.60.14 (2), tag `02IE`: the same dimension formula for an
unbundled family generating an ideal of definition. -/
@[stacks 02IE "(2)"]
#check @IsLocalRing.ringKrullDim_quotient_initialSegmentIdeal_eq_sub
