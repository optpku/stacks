module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf
import StacksCheckRecall

/-!
# Lemma 18.21.1

Compatibility facade for localization at an arbitrary sheaf.  The slice-topos
adjunction and the explicit module lower-shriek construction are ReasLib and
Mathlib API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/- Lemma 18.21.1 (1) (04IE): localization of a topos at `F` is the slice
topos, with lower shriek `Over.forget F` and inverse image `Over.star F`. -/
@[stacks 04IE "(1), slice adjunction"]
#check @Over.forgetAdjStar

@[stacks 04IE "(1), canonical ringed-topos morphism"]
#check @RingedSite.Localization.AtSheaf.toAmbient

#check @localizationMorphismOfTopoiIn
#check @RingedSite.Localization.AtSheaf.underlyingStructure
#check @Over.star
#check @Over.star_obj_left
#check @Over.star_obj_hom

/- Lemma 18.21.1 (2) (04IE): inverse image on module sheaves is restriction
to the category-of-elements localization. -/
@[stacks 04IE "(2), module inverse image"]
#check @SheafOfModules.Localization.AtSheaf.restriction

/- Lemma 18.21.1 (3) (04IE): lower shriek for set-valued sheaves is the
forgetful functor from the slice. -/
@[stacks 04IE "(3), set lower shriek"]
#check @Over.forget

/- Lemma 18.21.1 (4) (04IE): module lower shriek is the direct-sum
presheaf construction followed by sheafification. -/
@[stacks 04IE "(4), sheafification formula"]
#check @SheafOfModules.Localization.AtSheaf.lowerShriekSheafification

@[stacks 04IE "(4), direct-sum formula"]
#check @SheafOfModules.Localization.AtSheaf.LowerShriekPresheaf.coproductMap_isIso

#check @SheafOfModules.Localization.AtSheaf.lowerShriekSheafificationAdj
#check @SheafOfModules.Localization.AtSheaf.lowerShriekSheafificationIso
