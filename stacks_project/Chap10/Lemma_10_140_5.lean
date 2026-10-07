module

public import ReasLib.RingTheory.Smooth.AtPrime.Regularity
import StacksCheckRecall

/-!
# Lemma 10.140.5

@stack 00TV
-/

@[expose] public section

/- Lemma 10.140.5 [stacks 00TV]: canonical recall that smoothness at a prime with separable
residue field is equivalent to regularity of its prime localization. -/
@[stacks 00TV]
#check @Algebra.IsSmoothAt.iff_isRegularLocalRing_of_separableResidueField
