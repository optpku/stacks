/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement

@[expose] public section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

/- Lemma 7.39.1 (00YO): distinct raw sheaf-fiber sections of a directed inverse system remain
distinct after a directed refinement which lifts a specified element through a member of a finite
covering family.  The refinement is represented by the reusable `DirectedRefinement` bundle. -/
@[stacks 00YO] #check @DirectedRefinement.Separates.existsCoverLift

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
