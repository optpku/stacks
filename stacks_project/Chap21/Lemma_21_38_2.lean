module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Section
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FiberedCategoryOver.LocalizedSection

/- The localized projection is a named reusable morphism of topoi. -/
@[stacks 08P9 "localized projection"]
#check @projection

@[stacks 08P9 "localized projection section predicate"]
#check @IsSection
@[stacks 08P9 "localized projection section retraction"]
#check @IsSection.projection_comp
@[stacks 08P9 "localized projection section inverse image"]
#check @IsSection.inverseImage_eq_projectionPushforward

/- Lemma 21.38.2 (08P9): the localized projection has a section, and the
section inverse image is the localized projection direct image. -/
@[stacks 08P9]
#check @projection_exists

/- The section is induced by the canonical cleavage pullback on slices. -/
#check @Functor.Cleavage.SliceSection.Pullback.functor
#check @Functor.Cleavage.SliceSection.Pullback.adjunction
#check @Functor.Cleavage.SliceSection.Pullback.postIso

end CategoryTheory.FiberedCategoryOver.LocalizedSection
