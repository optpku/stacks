module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Surjective
import StacksCheckRecall

/-!
# Lemma 15.6.5

@stack 08IG

For a surjective ring-pullback situation, every component of the canonical adjunction unit is
surjective, but the unit need not be injective in general.
-/

@[stacks 08IG "surjectivity of the canonical module pullback map"]
#check @CategoryTheory.ModuleCat.Pullback.unit_app_surjective

@[stacks 08IG "the canonical module pullback map need not be injective"]
#check CategoryTheory.ModuleCat.Pullback.unit_app_not_injective_in_general
