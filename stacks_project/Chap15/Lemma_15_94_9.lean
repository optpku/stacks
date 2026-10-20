module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion.Principal
import StacksCheckRecall

/-!
# Lemma 15.94.9

@stack 0G3G
-/

@[expose] public section

/- Lemma 15.94.9 (1) (0G3G): the principal-power intersection annihilates the kernel of the
ordinary completion map of a derived-complete module. -/
@[stacks 0G3G "(1), principal-power intersection annihilates the completion kernel"]
#check @ModuleCat.IsDerivedCompleteWithRespectTo.principalPowerIntersection_smul_completionKer_eq_bot

/- Lemma 15.94.9 (2) (0G3G): for the derived-complete ring module, the principal-power
intersection is square-zero. -/
@[stacks 0G3G "(2), square-zero principal-power intersection"]
#check @ModuleCat.IsDerivedCompleteWithRespectTo.principalPowerIntersection_sq_eq_bot
