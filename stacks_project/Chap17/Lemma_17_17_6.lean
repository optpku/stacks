module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Localization
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Basic
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.6: the structure module on an open slice, extended by lower shriek, is flat. -/
@[stacks 05NH]
#check @SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_isFlat

/- Companion recall: the canonical lower-shriek structure module on a ringed site. -/
#check @SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero

/- Companion recall: the structure sheaf on an open subspace agrees with the pullback of the
ambient structure sheaf. -/
#check @AlgebraicGeometry.RingedSpace.openSubspaceRingSheafIso
