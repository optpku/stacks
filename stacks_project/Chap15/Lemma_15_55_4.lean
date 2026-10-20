module

public import ReasLib.Algebra.Category.ModuleCat.Injective.Ext
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.55.4

@stack 0AVF
-/

/-!
# Lemma 15.55.4: Baer's criterion through Ext

The reusable owner is the ideal-quotient specialization of the categorical degree-one Ext
criterion for injective objects.
-/

/- Lemma 15.55.4, tag `0AVF`: injectivity, vanishing of `Ext¹(R ⧸ I, J)` for every ideal `I`, and
Baer's criterion are equivalent. -/
@[stacks 0AVF]
#check @CategoryTheory.ModuleCat.injective_idealQuotient_ext_tfae

/- The direct two-clause criterion is the preferred downstream API. -/
#check @CategoryTheory.ModuleCat.injective_iff_idealQuotient_ext_one
