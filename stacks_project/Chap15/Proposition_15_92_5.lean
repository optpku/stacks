module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion.Hausdorff
import StacksCheckRecall

/-!
@stack 091T

Proposition 15.92.5 is recalled from the shared comparison between ordinary adic completeness,
derived completeness, and adic Hausdorffness.  The intersection criterion is owned separately by
the reusable `IsHausdorff` API.
-/

@[expose] public section

/- Proposition 15.92.5 (091T), in the commutative-ring `ModuleCat` formalization: adic completeness
is equivalent to derived completeness together with the vanishing intersection
`⋂ n, I ^ n M = 0`. -/
@[stacks 091T "adic completeness via derived completeness and separatedness"]
#check @ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_iInf_pow_smul_eq_bot

/- The same equivalence in terms of the canonical `IsHausdorff` predicate. -/
#check @ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff

/- Lemma 15.92.3 supplies the derived-completeness half of the comparison. -/
#check @ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete
#check @ModuleCat.surjective_adicCompletion_of_isDerivedCompleteWithRespectTo

/- The lower-level `031D` owner identifies Hausdorffness with the vanishing intersection. -/
#check @AdicCompletion.of_injective_iff
#check @IsHausdorff.of_iInf_pow_smul_eq_bot
