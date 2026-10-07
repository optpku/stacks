module

public import ReasLib.Topology.ConnectedComponents.Clopen
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.12 (formal owner): `Set.IsIntersectionOfClopens T` expresses that `T` is an
intersection of open and closed subsets. -/
@[stacks 04PL "intersections of open and closed subsets"]
#check Set.IsIntersectionOfClopens

/- Lemma 5.12.12 (formal owner): `Set.IsConnectedComponentSaturated T` expresses that `T` is a
union of connected components. -/
@[stacks 04PL "unions of connected components"]
#check Set.IsConnectedComponentSaturated

/- Lemma 5.12.12: in a quasi-compact prespectral quasi-separated space, the two source
descriptions are equivalent exactly when the subset is closed. -/
@[stacks 04PL "clopen intersections characterize closed unions of connected components"]
#check @Set.isIntersectionOfClopens_iff
