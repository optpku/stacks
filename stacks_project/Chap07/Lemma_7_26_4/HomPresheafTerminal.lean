module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.BaseChange
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized

/-!
# Terminal Hom-presheaf recall

Terminal evaluation and restriction are exposed by the localized Hom-sheaf
interface, with its canonical Hom-presheaf base-change calculation.
-/

@[expose] public section

#check @CategoryTheory.Pseudofunctor.PresheafHom.BaseChange.Inv.identitySlice
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.evalEquiv
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.terminalEquiv
