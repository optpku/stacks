module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf
import StacksCheckRecall

/-!
# Definition 18.21.2

Compatibility facade for the category-of-elements presentation of a ringed
site localized at a sheaf.
-/

@[expose] public section

open CategoryTheory

/- Definition 18.21.2 (04J2): the localized ringed site has the
category-of-elements topology and the inverse-image structure ring. -/
@[stacks 04J2 "localized ringed site"]
#check @RingedSite.Localization.AtSheaf.site

@[stacks 04J2 "inverse-image structure map"]
#check @RingedSite.Localization.AtSheaf.inverseImageStructureMap

/- The direct-image structure map is the adjoint transpose of the preceding
identity map, not a comparison with slice forgetful. -/
@[stacks 04J2 "direct-image structure map"]
#check @RingedSite.Localization.AtSheaf.structureMap

@[stacks 04J2 "ringed-topos localization"]
#check @RingedSite.Localization.AtSheaf.toAmbient

#check @RingedSite.Localization.AtSheaf.toAmbientForgetIso
#check @RingedSite.Localization.AtSheaf.structureMap_adjunct
#check @localizationMorphismOfTopoiIn
#check @sheafCategoryOfElementsEquivOver
