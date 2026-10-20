module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.Local
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.4.8 (tag 046N): for a fully faithful morphism of stacks over `(C, J)`, being an
equivalence over the base is equivalent to every target-fiber object being locally in the
essential image.  The source-facing owner is the bundled stack statement; the heterogeneous
cartesian theorem is its universe-polymorphic reusable companion. -/
@[stacks 046N]
#check @StackOver.Hom.IsEquivalence.iff_locallyEssentiallySurjective

#check @CartesianBasedFunctor.isEquivalence_iff_locallyEssentiallySurjective

end CategoryTheory
