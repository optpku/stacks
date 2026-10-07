module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.PowerTorsion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.94.8 (Bhatt) (0CQY)

@stack 0CQY
-/

/- Lemma 15.94.8 (Bhatt), Stacks `0CQY`: a derived-complete module which is power-torsion for a
finitely generated ideal is annihilated by one uniform power of that ideal. -/
@[stacks 0CQY "Lemma 15.94.8 (Bhatt), uniform power annihilation"]
#check @ModuleCat.IsDerivedCompleteWithRespectTo.exists_pow_smul_top_eq_bot_of_isIdealPowerTorsion
