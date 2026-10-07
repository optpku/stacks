module

public import ReasLib.RingTheory.Flat.Locus.QuotientPowers
import StacksCheckRecall

/-!
# Flatness along a closed subset from ideal-power quotients

Lemma 15.19.5 applies the local ideal-power criterion at every prime of
`V(I.map (algebraMap R S) + J)`.

@stack 05LU
-/

/- Lemma 15.19.5 (05LU): the source conclusion in its canonical flat-locus form. -/
@[stacks 05LU "Lemma 15.19.5"]
#check @Module.Flat.QuotientPowers.zeroLocus_add_subset_flatOverBaseLocus

/- The local criterion used at each prime of the closed subset. -/
@[stacks 0523 "local quotient-power criterion"]
#check @Module.Flat.QuotientPowers.atPrime
