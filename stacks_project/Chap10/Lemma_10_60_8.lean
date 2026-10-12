/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.DimensionOne
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.60.8: for a Noetherian local ring, dimension one, Hilbert--Samuel degree one, the
nonnilpotent closed-point equation, the nonnilpotent radical equation, and the minimal principal
ideal-of-definition criterion are equivalent.

@stack 00KK
-/

@[stacks 00KK "dimension-one TFAE"]
#check @Ideal.HilbertSamuel.dimensionOne_tfae

@[stacks 00KK "dimension and Hilbert-Samuel degree (canonical generic form)"]
#check @Ideal.HilbertSamuel.degree_eq_iff_ringKrullDim_eq

@[stacks 00KK "dimension and closed-point zero locus"]
#check @Ideal.HilbertSamuel.dimensionOne_iff_zeroLocus

@[stacks 00KK "zero-locus and principal radical bridge"]
#check @PrimeSpectrum.zeroLocus_singleton_eq_closedPoint_iff_radical

@[stacks 00KK "dimension and principal radical"]
#check @Ideal.HilbertSamuel.dimensionOne_iff_radical

@[stacks 00KK "dimension and minimal parameter ideal of definition"]
#check @Ideal.HilbertSamuel.dimensionOne_iff_parameterIdeal
