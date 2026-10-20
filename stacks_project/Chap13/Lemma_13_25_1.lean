module

import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Localization
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.25.1

The source statement is a specialization of the model-independent localization
API for a functorial bounded-below injective resolution.  The reusable owner
does not require the target to be a derived category or the input functor to
come from an additive functor: it applies to every functor out of
`HomotopyCategory.Plus A`.
-/

open CategoryTheory

/- Lemma 13.25.1 (Stacks 05TN): after lifting a functorial injective resolution
through `K⁺(A) ⥤ D⁺(A)`, the composite through bounded-below injective homotopy
objects is a right derived functor.  Taking
`G = F.toBoundedBelowDerived` gives the textbook triangle for an additive
functor `F : A ⥤ B`. -/
@[stacks 05TN] #check
  @HomotopyCategory.Plus.InjectiveResolutionFunctor.lift_comp_isRightDerivedFunctor

#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.liftComparison
#check @Functor.toBoundedBelowDerived

end
