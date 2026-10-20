module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.Family
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized
public import ReasLib.CategoryTheory.Sites.Descent.TypeSheaf

/-!
# Direct-source comparison recall

The former 4,000-line direct comparison was a proof-local presentation of
effective descent. Its stable downstream API is the stack theorem, family
descent pullback, localized Hom glueing, and cover transport imported here.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.isStack
#check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.toDescentData_essSurj
#check @CategoryTheory.DescentDatum.Pullback.canonicalIso
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.existsUnique_of_compatible
#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver
