module

public import ReasLib.RingTheory.DiscreteValuationRing.Characterization
import StacksCheckRecall

/-!
# Characterizations of Discrete Valuation Rings

@stack 00PD
-/

@[expose] public section

/- Lemma 10.119.7 (1): the five standard characterizations of a discrete valuation ring are
equivalent. -/
@[stacks 00PD]
#check @discreteValuationRing_tfae

/- Lemma 10.119.7 (2): after choosing a generator `π` of the maximal ideal, every nonzero
element has a unique expression `u * π ^ n` with `u` a unit. -/
@[stacks 00PD]
#check @IsDiscreteValuationRing.existsUnique_unit_mul_pow

#check @IsDiscreteValuationRing.iff_regularLocalRing_dim_one
#check @IsDiscreteValuationRing.iff_maximalIdeal_isPrincipal
#check @IsDiscreteValuationRing.iff_integrallyClosed_dim_one
#check @discreteValuationRing_iff_regularLocalRing_dim_one
