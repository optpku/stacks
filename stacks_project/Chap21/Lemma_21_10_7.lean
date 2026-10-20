module

public import ReasLib.CategoryTheory.Sites.Cech.AcyclicIntersections
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

/- Lemma 21.10.7 (Tag 03F7): if all positive-degree cohomology objects vanish on the iterated
Čech intersections of a covering family, the normalized positive-degree Čech-to-site comparison
is an isomorphism. -/

@[stacks 03F7 "acyclic intersections for a Cech covering"]
#check @CategoryTheory.HasAcyclicCechIntersections

#check @CategoryTheory.HasAcyclicCechIntersections.isZero

@[stacks 03F7 "Cech comparison isomorphism from acyclic intersections"]
#check @CategoryTheory.cechCohomology_iso_siteCohomology_of_acyclic_intersections

#check @CategoryTheory.Cech.IsComparison.isIso_of_acyclic_intersections
