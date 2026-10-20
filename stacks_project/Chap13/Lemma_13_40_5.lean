module

import ReasLib.CategoryTheory.Pretriangulated.Subcategory.Orthogonal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.40.5

The owner-level statement is the canonical triangulated-instance closure of
`extensionProduct A A.rightOrthogonal`; the individual triangle and
binary-coproduct clauses follow from the `ObjectProperty.IsTriangulated` API.
-/

@[stacks 0CQR] #check @CategoryTheory.ObjectProperty.extensionProduct_rightOrthogonal_isTriangulated
