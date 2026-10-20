module

public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Section
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FiberedCategoryOver.LocalizedSection

/- The localized comparison and the induced target section are named data. -/
@[stacks 08PB "localized comparison"]
#check @comparison

@[stacks 08PB "base relocalization"]
#check @baseRelocalization

@[stacks 08PB "induced target section"]
#check @targetSection

@[stacks 08PB "localized section compatibility predicate"]
#check @IsCompatible
@[stacks 08PB "source section retraction"]
#check @IsCompatible.projection_comp
@[stacks 08PB "target section retraction"]
#check @IsCompatible.target_projection_comp
@[stacks 08PB "source section inverse image"]
#check @IsCompatible.inverseImage_eq_projectionPushforward
@[stacks 08PB "target section inverse image"]
#check @IsCompatible.targetInverseImage_eq_projectionPushforward

/- Lemma 21.38.4 (08PB): the section at the source of a morphism of fibred
categories and its induced target section satisfy the two retraction and the
two inverse-image/direct-image identities. -/
@[stacks 08PB]
#check @comparison_exists

/- The localized comparison and its base-object transport are canonical
parts of the inherited-ringed-site morphism. -/
#check @Functor.inheritedRingedSiteHom.projection_obj
#check @Functor.inheritedRingedSiteHom.localization_isContinuous
#check @Functor.inheritedRingedSiteHom.localization_preservesFiniteLimits

end CategoryTheory.FiberedCategoryOver.LocalizedSection
