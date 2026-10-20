module

public import ReasLib.Topology.Jacobson.LocallyConstructible
import StacksCheckRecall

@[expose] public section

/- Lemma 5.18.5 (1): open subspaces of a Jacobson space are Jacobson. -/
@[stacks 005X "(1) open subspaces"]
#check @IsOpen.jacobsonSpace_subtype

/- Lemma 5.18.5 (2): closed subspaces of a Jacobson space are Jacobson. -/
@[stacks 005X "(2) closed subspaces"]
#check @IsClosed.jacobsonSpace_subtype

/- Lemma 5.18.5 (3): locally closed subspaces of a Jacobson space are Jacobson. -/
@[stacks 005X "(3) locally closed subspaces"]
#check @IsLocallyClosed.jacobsonSpace_subtype

/- Lemma 5.18.5 (4): unions of locally closed subspaces are Jacobson. -/
@[stacks 005X "(4) unions of locally closed subspaces"]
#check @IsUnionOfLocallyClosed.jacobsonSpace_subtype

/- Lemma 5.18.5 (5): constructible subspaces are Jacobson. -/
@[stacks 005X "(5) constructible subspaces"]
#check @Topology.IsConstructible.jacobsonSpace_subtype

/- Lemma 5.18.5 (6): a locally union-of-locally-closed subspace is Jacobson. -/
@[stacks 005X "(6) locally unions of locally closed subspaces"]
#check @IsLocallyUnionOfLocallyClosed.jacobsonSpace_subtype

/- In every case, closed points of the subspace are closed in the ambient space. -/
@[stacks 005X "closed points of open subspaces"]
#check @IsOpen.closedPoints_subset_preimage_closedPoints
@[stacks 005X "closed points of closed subspaces"]
#check @IsClosed.closedPoints_subset_preimage_closedPoints
@[stacks 005X "closed points of locally closed subspaces"]
#check @IsLocallyClosed.closedPoints_subset_preimage_closedPoints
@[stacks 005X "closed points of unions of locally closed subspaces"]
#check @IsUnionOfLocallyClosed.closedPoints_subset_preimage_closedPoints
@[stacks 005X "closed points of constructible subspaces"]
#check @Topology.IsConstructible.closedPoints_subset_preimage_closedPoints
@[stacks 005X "closed points of locally unions of locally closed subspaces"]
#check @IsLocallyUnionOfLocallyClosed.closedPoints_subset_preimage_closedPoints
