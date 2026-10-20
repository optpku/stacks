module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Restriction.Equivalence
import StacksCheckRecall

/-!
# Lemma 15.92.25: flat base change and derived completion

@stack 0925

The restriction functor and its equivalence criterion are owned by the shared derived-completion
API.  This file records the source statement directly.
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.92.25 (Stacks `0925`): a flat ring map inducing an isomorphism modulo a finitely
generated ideal gives an equivalence on the corresponding derived-complete subcategories. -/
@[stacks 0925 "derived-complete restriction equivalence"]
#check @DerivedCategory.DerivedComplete.Restriction.isEquivalence_of_flat_of_quotientMap_bijective

@[stacks 0925 "restriction functor on derived-complete objects"]
#check @DerivedCategory.DerivedComplete.Restriction.functor

end
