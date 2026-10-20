module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback

/-!
# Source reindexing recall

Reindexing descent data is owned by `DescentDatum.Pullback`; cover-arrow
index changes are owned by `Cover.Arrow.mapOver`.
-/

@[expose] public section

#check @CategoryTheory.DescentDatum.Pullback.functor
#check @CategoryTheory.DescentDatum.Pullback.iso
#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver_comp
