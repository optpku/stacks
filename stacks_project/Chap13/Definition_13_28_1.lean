module

import ReasLib.CategoryTheory.Pretriangulated.K0.GrothendieckGroup
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Definition 13.28.1

Definition 13.28.1 defines the triangulated zeroth Grothendieck group.  Its
canonical quotient presentation and exact-functorial API live in
`ReasLib.CategoryTheory.Pretriangulated.K0.GrothendieckGroup`, independently of Chapter 13.
-/

/- Definition 13.28.1: `K₀(C)` is the quotient of the free abelian group on the objects of a
pretriangulated category by the relations `[Y] - [X] - [Z]` from distinguished triangles
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧`. -/
@[stacks 0FCN] #check @CategoryTheory.TriangulatedK0

#check @CategoryTheory.TriangulatedK0.relation
#check @CategoryTheory.TriangulatedK0.relations
#check @CategoryTheory.TriangulatedK0.relation_mem_relations
#check @CategoryTheory.TriangulatedK0.of
#check @CategoryTheory.TriangulatedK0.lift
#check @CategoryTheory.TriangulatedK0.lift_of
#check @CategoryTheory.TriangulatedK0.of_distinguished
#check @CategoryTheory.TriangulatedK0.map
#check @CategoryTheory.TriangulatedK0.map_of
#check @CategoryTheory.TriangulatedK0.map_id
#check @CategoryTheory.TriangulatedK0.map_comp
