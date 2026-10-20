module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.126.7

@stack 0BWW

The Hilbert--Samuel multiplicity bound is owned by the parameter-ideal API in
ReasLib.  This chapter entry records the source label and exact reusable type.
-/

/- Lemma 15.126.7: the multiplicity of a parameter ideal is bounded by its colength. -/
@[stacks 0BWW "Lemma 15.126.7, parameter-ideal multiplicity bound"]
#check @Ideal.HilbertSamuel.multiplicity_le_quotient_length_of_parameters
