module

public import ReasLib.Algebra.Module.IdealProjective.Ext
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.71.3: ideal-projectivity and `Ext¹`

The TFAE below is the source-facing aggregation.  Atomic equivalences and the positive-degree
annihilator theorem are the reusable downstream interface.

@stack 0G92
-/

/- Lemma 15.71.3: ideal-projectivity, free factorisation of scalar endomorphisms, and
annihilation of all `Ext¹` groups are equivalent. -/
@[stacks 0G92]
#check @Module.IsIdealProjective.tfae

/- Atomic free-factorisation view. -/
#check @Module.IsIdealProjective.iff_factorsThroughFree

/- Atomic `Ext¹`-annihilator view. -/
#check @Module.IsIdealProjective.iff_ext_one_annihilator

/- The forward implication is reusable in every positive degree. -/
#check @Module.IsIdealProjective.le_annihilator_ext

/- Strong ideal-valued form: all degree-one extension annihilators recover the complete
projective-factor ideal. -/
#check @Module.projectiveFactorIdeal.eq_iInf_annihilator_ext_one

/- Generic linear-abelian owner behind the module specialization. -/
#check @CategoryTheory.idealProjective.iff_ext_one_annihilator
