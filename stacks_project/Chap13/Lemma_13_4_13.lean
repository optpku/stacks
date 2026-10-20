module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Coproduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.13

The reusable owner is `CategoryTheory.Pretriangulated.coproductTriangle` and
its distinguishedness theorem.  This source-facing file keeps the Stacks label
as a direct checked bridge.
-/

/- Lemma 13.4.13 (Stacks 0CRG): objectwise coproducts of distinguished
triangles are distinguished. -/
@[stacks 0CRG] #check @CategoryTheory.Pretriangulated.coproductTriangle_distinguished

#check @CategoryTheory.Pretriangulated.coproductTriangle
#check @CategoryTheory.Pretriangulated.coproductTriangle.ι
#check @CategoryTheory.Pretriangulated.coproductTriangle.desc
#check @CategoryTheory.Pretriangulated.coproductTriangle.isColimitCofan
