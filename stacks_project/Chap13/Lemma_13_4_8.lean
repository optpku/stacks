/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.TriangleMorphism.Uniqueness
import StacksCheckRecall

@[expose] public section

/- Lemma 13.4.8 is owned by the reusable triangle-morphism uniqueness API. -/
@[stacks 0FWZ] #check
  @CategoryTheory.Pretriangulated.TriangleMorphism.hom₂_eq_of_hom_vanishing
#check @CategoryTheory.Pretriangulated.TriangleMorphism.ext_of_outer_eq_of_hom_vanishing

end
