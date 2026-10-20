module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Presentation
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.3.1

The source presentation chooses pairwise and triple overlaps.  The reusable owner is split into
the canonical descent-data object and a thin chosen-overlap presentation; the chapter entry is a
recall block so it cannot introduce a second descent-data hierarchy.
-/

namespace CategoryTheory

/- Chosen pairwise and triple overlaps provide the literal textbook presentation. -/
#check @SemiRepresentableFamily.Over.OverlapPresentation

#check @Presieve.HasPairwisePullbacks
#check @SemiRepresentableFamily.Over.HasTripleOverlaps
#check @SemiRepresentableFamily.Over.OverlapPresentation.ofChosenTriples
#check @SemiRepresentableFamily.Over.OverlapPresentation.ofHasOverlaps
#check @SemiRepresentableFamily.Over.OverlapPresentation.ofHasOverlaps_pairwise
#check @SemiRepresentableFamily.Over.OverlapPresentation.ofHasOverlaps_triple
#check @SemiRepresentableFamily.Over.OverlapPresentation.nonemptyOfHasOverlaps
#check @SemiRepresentableFamily.Over.OverlapPresentation.nonemptyOfPullbacks

/- Definition 8.3.1 (026B): the canonical descent-data category packages its objects, their
cocycle condition, and compatible morphisms without making overlap choices part of the owner. -/
@[stacks 026B "descent-data category"]
#check @DescentDatum

/- The chosen-overlap category and its equivalence expose the source's literal presentation. -/
#check @DescentDatum.Chosen

#check @DescentDatum.Chosen.equivalence

#check @DescentDatum.Chosen.toCanonical
#check @DescentDatum.Chosen.toCanonical_obj_obj
#check @DescentDatum.Chosen.toCanonical_map_hom
#check @DescentDatum.Chosen.toCanonical_obj_hom
#check @DescentDatum.Chosen.fromCanonical
#check @DescentDatum.Chosen.fromCanonical_obj_obj
#check @DescentDatum.Chosen.fromCanonical_map_hom
#check @DescentDatum.Chosen.fromCanonical_obj_hom

end CategoryTheory
