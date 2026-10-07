module

public import ReasLib.CategoryTheory.Sites.Cover.Family
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized

/-!
# Terminal-cover recall

The fixed-cover family has a canonical sieve view, and compatible local Hom
morphisms glue uniquely through the localized Hom API.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.Cover.family_toSieve
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.coverSieve_overEquiv
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.existsUnique_of_compatible
