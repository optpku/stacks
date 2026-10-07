module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCheckRecall

@[expose] public section

/- Definition 7.7.6: a presheaf `F` on a site `(C, J)` valued in a category `A` is a sheaf
iff for every object `X` of `A` the Hom-valued presheaf of types
`F_X := F ⋙ coyoneda.obj (op X)` is a sheaf of types. -/
@[stacks 00VR] #check CategoryTheory.Presheaf.IsSheaf
