module

public import ReasLib.RingTheory.MvPolynomial.Spectrum
import StacksCheckRecall

/-!
# Lemma 15.21.4

@stack 0532
-/

@[expose] public section

-- Lemma 15.21.4: the spectrum image of a split multivariate-polynomial quotient is the zero
-- locus of the intersection of its evaluation ideals.
@[stacks 0532]
#check @MvPolynomial.range_comap_quotient_eq_zeroLocus_iInf_eval
