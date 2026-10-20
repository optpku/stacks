module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.FiniteRefinement

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

/- Proposition 7.39.3 (00YQ): a site with finite limits whose covering sieves admit finite
covering refinements has enough points.  Finite refinement is the canonical
`HasFiniteRefinement` owner, and enough points is its reusable consequence. -/
@[stacks 00YQ] #check @HasFiniteRefinement.hasEnoughPoints

/- The finite-family lifting bridge upgrades the hypothesis used by the refinement construction
to the sieve-lifting condition of the canonical point constructor. -/
#check @Point.Fiber.of_finite_cover_lifts

end CategoryTheory.GrothendieckTopology
