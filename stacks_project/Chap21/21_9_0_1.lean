module

public import ReasLib.CategoryTheory.Sites.Cech.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- 21.9.0.1 (Tag 03AP): fixing a family in `Over U` gives the Cech-complex functor on
presheaves. Taking the coefficient category to be `AddCommGrpCat` recovers the source functor
from abelian presheaves to bounded-below cochain complexes. -/
@[stacks 03AP "Cech-complex functor on presheaves"]
#check @CategoryTheory.cechComplexOnPresheaves

/- Evaluation and natural-transformation glue for downstream use. -/
#check @CategoryTheory.cechComplexOnPresheaves_obj
#check @CategoryTheory.cechComplexOnPresheaves_obj_X
#check @CategoryTheory.cechComplexOnPresheaves_map

end
