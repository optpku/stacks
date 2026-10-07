module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Localization
import StacksCheckRecall

/-!
# Lemma 18.28.7

The module represented by an object is the slice unit module extended by lower shriek.  The
construction and its flatness theorem are reusable for both presheaves and sheaves.
-/

@[expose] public section

open SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

/- Lemma 18.28.7 (03EV), presheaves: the extended slice structure module is flat. -/
@[stacks 03EV "presheaf"]
#check @PresheafOfModules.Localization.structureModule_isFlat

/- Lemma 18.28.7 (03EV), sheaves: the extended slice structure module is flat. -/
@[stacks 03EV "sheaf"]
#check @SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_isFlat

/- The reusable owner of the sheaf object itself, for which the global `j![𝒪, U]` notation is
provided. -/
#check @SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero
