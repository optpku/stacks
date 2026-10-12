/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.CategoryCohomology.Computation
import StacksCheckRecall

@[expose] public section

/-!
# Example 21.42.1: computing category cohomology

The composable-arrow complex is owned by `CategoryCohomology.Bar`.  It is functorial and exact in
the coefficient presheaf, defines a universal cohomological delta functor, and computes
`Sheaf.functorH` after specializing to the chaotic topology.
-/

open CategoryTheory

/- Example 21.42.1 (Computing cohomology) (08RZ): the cohomology functors on the chaotic site are
computed functorially by the composable-arrow bar complex. -/
@[stacks 08RZ]
#check @CategoryCohomology.Chaotic.functor_isomorphic

#check @CategoryCohomology.Bar.cosimplicialObject
#check @CategoryCohomology.Bar.cosimplicialObject_map_π
#check @CategoryCohomology.Bar.cosimplicialMap
#check @CategoryCohomology.Bar.cosimplicialMap_app_π
#check @CategoryCohomology.Bar.complex
#check @CategoryCohomology.Bar.complexFunctor_exact
#check @CategoryCohomology.Bar.deltaFunctor
#check @CategoryCohomology.Bar.deltaFunctor.isUniversal
#check @CategoryCohomology.Chaotic.isomorphic_homology_complex
#check @CategoryCohomology.Chaotic.pointSkyscraper_cohomology_isZero_of_pos
#check @CategoryCohomology.Chaotic.pointSkyscraper_sheafCohomology_isZero_of_pos

end
