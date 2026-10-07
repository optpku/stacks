module

public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized
public import ReasLib.CategoryTheory.Sites.Descent.PullHom.Computations

/-!
# Terminal restriction normalization recall

The stable normalization layer is the generic `pullHom` calculation plus the
objectwise localized Hom restriction map.
-/

@[expose] public section

#check @CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map_of_fac
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.restrict
