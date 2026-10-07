module

public import ReasLib.CategoryTheory.Sites.Torsor
import StacksCheckRecall

/-!
# Definition 21.4.1 compatibility

The general site-torsor API is owned by `ReasLib.CategoryTheory.Sites.Torsor`.
-/

/- Definition 21.4.1 (03AH): a torsor is a pseudo-torsor with locally nonempty fibers. -/
@[stacks 03AH "site torsor"]
#check @CategoryTheory.Sheaf.Torsor

@[stacks 03AH "pseudo torsor underlying a torsor"]
#check @CategoryTheory.Sheaf.PseudoTorsor

@[stacks 03AJ "torsor isomorphism classes"]
#check @CategoryTheory.Sheaf.Torsor.IsoClasses
