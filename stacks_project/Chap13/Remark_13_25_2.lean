module

import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Remark 13.25.2

The textbook factorization is an exact functor into the bounded-below
homotopy category, not a strict equality obtained by simplifying the identity
functor on the target.  Its owner is the localization-lift API for functorial
injective resolutions.
-/

/- Remark 13.25.2 (Stacks 05TN): if a functorial bounded-below injective
resolution is lifted through a triangulated localization of `K⁺(𝒜)`, then
applying an additive `F : 𝒜 ⥤ ℬ` gives an exact factorization
`D⁺(𝒜) ⥤ K⁺(ℬ)`. -/
@[stacks 05TN] #check
  @HomotopyCategory.Plus.InjectiveResolutionFunctor.lift_comp_mapHomotopyCategoryPlus_exact

#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.lift_exact
#check @Functor.hasTriangulatedStructure_of_precomp_iso

end
