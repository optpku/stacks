module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Cohomology
import StacksCheckRecall

/-!
# Cohomology of the extended alternating Cech complex

@stack 0G6K
-/

@[expose] public section

/- Lemma 15.29.5 (1): cohomology vanishes above the length of the family. -/
@[stacks 0G6K "Lemma 15.29.5 (1)"]
#check @LocalizedModule.Away.Cech.Alternating.Cohomology.isZero_of_gt

/- Lemma 15.29.5 (2): every class is killed by a positive power of every generator. -/
@[stacks 0G6K "Lemma 15.29.5 (2)"]
#check @LocalizedModule.Away.Cech.Alternating.Cohomology.exists_pow_smul_eq_zero

/- Lemma 15.29.5 (3): cohomology is supported on the common zero locus. -/
@[stacks 0G6K "Lemma 15.29.5 (3)"]
#check @LocalizedModule.Away.Cech.Alternating.Cohomology.support_subset_zeroLocus

/- Lemma 15.29.5 (4): an invertible element in the generated ideal forces vanishing. -/
@[stacks 0G6K "Lemma 15.29.5 (4)"]
#check @LocalizedModule.Away.Cech.Alternating.Cohomology.isZero_of_exists_isUnit_span
