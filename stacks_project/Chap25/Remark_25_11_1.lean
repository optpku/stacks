module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Restriction
import StacksCheckRecall

@[expose] public section

/-!
This remark is a source-facing check of the reusable simplicial open-hypercovering API.
-/

/- Remark 25.11.1 [stacks 01H5], empty-intersection clause: an empty matching family is
permitted when the finite intersection to be covered is empty. -/
@[stacks 01H5 "empty matching covering"] #check
  @SSet.OpenHypercovering.Intersection.emptyCover

/- Conversely, an empty matching family in a hypercovering forces the prescribed intersection
to be empty. -/
#check @SSet.OpenHypercovering.Intersection.iInf_eq_bot_of_isEmpty_matchingIndices

/- Remark 25.11.1 [stacks 01H5], nonempty-index sub-simplicial set. -/
@[stacks 01H5 "nonempty-index sub-simplicial set"] #check
  SSet.OpenFamily.nonemptySubfunctor
#check SSet.OpenFamily.restrictToNonempty

/- Remark 25.11.1 [stacks 01H5], explicit refinement to the nonempty indices. -/
@[stacks 01H5 "refinement to nonempty opens"] #check
  SSet.OpenHypercovering.restrictToNonempty.refines

/- The refinement map is the canonical subfunctor inclusion. -/
#check SSet.OpenFamily.nonemptyInclusion
#check SSet.OpenHypercovering.restrictToNonempty.family_eq_restrict

/- Every open in the restricted hypercovering is nonempty. -/
#check SSet.OpenHypercovering.restrictToNonempty.degreewiseNonempty
