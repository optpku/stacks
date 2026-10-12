/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Ext
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 21.13.4 (Tag 072Y): an abelian sheaf is totally acyclic when its positive
cohomology over every sheaf of sets vanishes. -/
@[stacks 072Y "totally acyclic abelian sheaf"]
#check @CategoryTheory.Sheaf.IsTotallyAcyclic

/- The class specification and the presheaf-level vanishing projection are reusable companions. -/
#check @CategoryTheory.Sheaf.isTotallyAcyclic_iff
#check @CategoryTheory.Sheaf.IsTotallyAcyclic.isZero_higherCohomologyOverSheaf
#check @CategoryTheory.Sheaf.IsTotallyAcyclic.isZero_higherCohomologyOverPresheaf

end
