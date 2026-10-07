module

public import ReasLib.CategoryTheory.Sites.Cover.Family
public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.Family
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized
public import ReasLib.CategoryTheory.Sites.Descent.TypeSheaf

/-!
# Legacy fixed-cover construction recall

This compatibility import deliberately exposes only reusable ReasLib owners.
The former Chapter 7 proof decomposition no longer forms a downstream API.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.Cover.family
#check @CategoryTheory.GrothendieckTopology.Cover.Relation.mapOver
#check @CategoryTheory.DescentDatum.Pullback.functor
#check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.isStack
