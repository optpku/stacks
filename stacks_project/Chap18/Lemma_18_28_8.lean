module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Generators
import StacksCheckRecall

/-!
# Lemma 18.28.8

Localized structure modules generate the presheaf and sheaf module categories.  The reusable
leaf also exposes the consequence needed by homological constructions: every object admits an
epimorphism from a flat object.
-/

@[expose] public section

/- Lemma 18.28.8 (03EW), presheaves: localized structure modules give epimorphic
presentations. -/
@[stacks 03EW "presheaf localized generators"]
#check @PresheafOfModules.exists_epi_from_coproduct_structureModule

/- Lemma 18.28.8 (03EW), presheaves: every object has a flat epimorphic cover. -/
@[stacks 03EW "presheaf flat cover"]
#check @PresheafOfModules.exists_epi_from_flat

/- Lemma 18.28.8 (03EW), sheaves: localized structure modules give epimorphic presentations. -/
@[stacks 03EW "sheaf localized generators"]
#check @SheafOfModules.RingedSite.exists_epi_from_coproduct_structureModule

/- Lemma 18.28.8 (03EW), sheaves: every object has a flat epimorphic cover. -/
@[stacks 03EW "sheaf flat cover"]
#check @SheafOfModules.RingedSite.exists_epi_from_flat
