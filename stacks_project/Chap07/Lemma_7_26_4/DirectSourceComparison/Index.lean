module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.BaseChange
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized
public import ReasLib.CategoryTheory.Sites.Descent.TypeSheaf

/-!
# Direct-source comparison recall

The former Chapter 7 direct-source construction has no independent consumer.
Its stable ingredients are the reusable cover transport, family descent
pullback, localized Hom, and effective descent interfaces imported here.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver
#check @CategoryTheory.DescentDatum.Pullback.canonicalIso
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.restrict
#check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.toDescentData_essSurj
