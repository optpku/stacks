module

public import ReasLib.RingTheory.FittingIdeal.Support.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Supports of Finitely Presented Modules

@stack 051B
-/

/- Companion recall: the owner object for the textbook support of an `R`-module is
`Module.support R M`. -/
@[stacks 051B "support owner"]
#check @Module.support

/- Companion recall: for a finitely presented `R`-module, the canonical owner ideal cutting out
the support is the zeroth Fitting ideal `fittingIdeal R M 0`. -/
@[stacks 051B "Fitting ideal owner"]
#check @fittingIdeal

/- Companion recall: the support of a finite module is canonically the zero locus of its zeroth
Fitting ideal. This is the source-faithful bridge used in Lemma 10.40.8. -/
@[stacks 051B "support zero-locus bridge"]
#check @Module.zeroLocus_fittingIdeal_zero_eq_support

/- Companion recall: finite presentation makes the zeroth Fitting ideal finitely generated. -/
@[stacks 051B "finite-generation bridge"]
#check @Module.FinitePresentation.fittingIdeal_fg

/- Companion recall: finite modules have closed support. Since finitely presented modules are
finite, this supplies the closedness half of Lemma 10.40.8 directly from the owner abstraction
`Module.support`. -/
@[stacks 051B "closed support owner"]
#check @Module.isClosed_support

/- Companion recall: on `Spec R`, compact open subsets are exactly complements of zero loci of
finitely generated ideals. This is the ambient compact-open owner theorem used to package the
quasi-compactness conclusion. -/
@[stacks 051B "compact-open owner"]
#check @PrimeSpectrum.isCompact_isOpen_iff_ideal

/- Lemma 10.40.8: the support of a finitely presented module is closed and
its complement is compact. -/
@[stacks 051B]
#check @Module.isClosed_support_and_isCompact_compl_support
