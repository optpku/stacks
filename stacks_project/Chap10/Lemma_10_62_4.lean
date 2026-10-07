module

public import ReasLib.RingTheory.Module.Support.IdealPower
import StacksCheckRecall

/-!
# Lemma 10.62.4

@stack 00L6
-/

@[expose] public section

/- Lemma 10.62.4, tag `00L6`: the finite-module support/zero-locus criterion is owned by
`Module.exists_pow_le_annihilator_iff_support_subset_zeroLocus` and its action-form companion. -/
@[stacks 00L6 "finite-module support and ideal powers"]
#check @Module.exists_pow_le_annihilator_iff_support_subset_zeroLocus

@[stacks 00L6 "finite-module support and ideal-power action"]
#check @Module.exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus

/- API design: the ReasLib owner is stated for an arbitrary finitely generated ideal.  This recall
keeps the chapter label while avoiding a chapter-only proof or a list-specific wrapper. -/

end
