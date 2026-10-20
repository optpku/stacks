module

import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Derived Comparison for a Weak Serre Subcategory

The unbounded comparison functor associated to 13.17.1.1 is owned by
`DerivedCategory.CohomologyIn.Comparison`.
-/

open CategoryTheory

/- 13.17.1.1: the derived functor of a weak Serre inclusion lands in the
ambient cohomology-in subcategory. -/
@[stacks 06UR] #check @DerivedCategory.CohomologyIn.Comparison.functor

/- Companion check: the objectwise landing statement is separately reusable. -/
@[stacks 06UR] #check @DerivedCategory.CohomologyIn.Comparison.obj_mem

/- Companion check: forgetting the lift recovers the ordinary derived functor. -/
@[stacks 06UR] #check @DerivedCategory.CohomologyIn.Comparison.compιIso

/- Companion computations: the comparison exposes the ordinary derived image
on both objects and morphisms. -/
@[stacks 06UR] #check @DerivedCategory.CohomologyIn.Comparison.functor.obj_obj

@[stacks 06UR] #check @DerivedCategory.CohomologyIn.Comparison.functor.map_hom
