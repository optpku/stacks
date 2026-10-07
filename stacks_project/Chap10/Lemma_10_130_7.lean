module

import StacksCheckRecall
public import ReasLib.RingTheory.CohenMacaulay.Fiber.BaseChange

@[expose] public section

/-!
# Cohen--Macaulay Fiber Locus under Base Change Recall

The source statement is the setwise form of the reusable pointwise
tensor-product base-change API for Cohen--Macaulay residue-field fibers.

@stack 00RK
-/

/- Lemma 10.130.7, tag 00RK: for a finite-type map `R → S` and arbitrary base change
`R → R'`, the Cohen--Macaulay fiber locus of `R' ⊗[R] S` is the inverse image of the
corresponding locus of `S/R`. -/
@[stacks 00RK "Cohen-Macaulay fiber locus and base change"]
#check @PrimeSpectrum.cohenMacaulayFiberLocus_preimage_includeRight_eq_baseChange

/- Lemma 10.130.7, pointwise form: membership in the locus is preserved and reflected at every
prime of the tensor-product base change. -/
@[stacks 00RK "Cohen-Macaulay fiber locus and base change"]
#check @PrimeSpectrum.mem_cohenMacaulayFiberLocus_baseChange_iff
