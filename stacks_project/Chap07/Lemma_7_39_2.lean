/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation

@[expose] public section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

/- Lemma 7.39.2 (00YP): distinct raw sheaf-fiber sections remain distinct after a directed
refinement whose induced fiber map has lifts through every finite covering family. -/
@[stacks 00YP] #check @DirectedRefinement.Separates.existsFiniteCoverLifts

/- The stronger reusable companion gives finite-cover lifts for every target-fiber element, not
only for the image of the original system. -/
#check @DirectedRefinement.Separates.Target.existsFiniteCoverLifts

/- After finite refinement turns those lifts into sieve lifting, this owner constructs the
resulting point without rebuilding the inverse-system fiber infrastructure. -/
#check @DirectedInverseSystem.FiniteCoverLifts.point

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
