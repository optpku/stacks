module

import ReasLib.CategoryTheory.Pretriangulated.ThreeByThree
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 13.4.23

The reusable owner is `CategoryTheory.Pretriangulated.ThreeByThree`.  It keeps
the six distinguished-triangle views, four comparison morphisms of triangles,
and the signed lower-right compatibility independently of the chapter proof.
-/

/- Proposition 13.4.23 (Stacks 05R0): a commutative square in a triangulated category extends
to a distinguished three-by-three diagram. -/
@[stacks 05R0] #check @CategoryTheory.Pretriangulated.ThreeByThree.nonempty_of_commSq

@[stacks 05R0] #check @CategoryTheory.Pretriangulated.ThreeByThree
#check @CategoryTheory.Pretriangulated.ThreeByThree.topRow
#check @CategoryTheory.Pretriangulated.ThreeByThree.middleRow
#check @CategoryTheory.Pretriangulated.ThreeByThree.leftColumn
#check @CategoryTheory.Pretriangulated.ThreeByThree.middleColumn
#check @CategoryTheory.Pretriangulated.ThreeByThree.bottomRow
#check @CategoryTheory.Pretriangulated.ThreeByThree.rightColumn
#check @CategoryTheory.Pretriangulated.ThreeByThree.topToMiddle
#check @CategoryTheory.Pretriangulated.ThreeByThree.middleToBottom
#check @CategoryTheory.Pretriangulated.ThreeByThree.leftToMiddle
#check @CategoryTheory.Pretriangulated.ThreeByThree.middleToRight

end
