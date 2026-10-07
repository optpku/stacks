module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- The canonical theorem has exactly the source's continuous-surjection and proper-closed-image
hypotheses, with no separation or compactness assumptions, and states the same closure inclusion.
Recalling it avoids a parallel source wrapper while exporting the topology API used by later items.
-/

/- Lemma 5.26.2: if `ρ` is a continuous surjection satisfying the Zorn-subset condition, then
for any open `G`, the image `ρ '' G` is contained in the closure of the complement of
`ρ '' Gᶜ`. This is exactly the canonical mathlib theorem
`image_subset_closure_compl_image_compl_of_isOpen`. -/
@[stacks 08YJ "closure containment for the image of an open set"]
#check image_subset_closure_compl_image_compl_of_isOpen
