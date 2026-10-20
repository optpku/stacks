module

public import Mathlib.Topology.Connected.TotallyDisconnected
import StacksCheckRecall

@[expose] public section

/- Definition 5.7.8: a totally disconnected topological space is represented by the canonical
mathlib class `TotallyDisconnectedSpace`. -/
@[stacks 04MC "totally disconnected topological spaces"]
#check @TotallyDisconnectedSpace

/- The source formulation, saying that every connected component is a singleton, is the canonical
characterization of `TotallyDisconnectedSpace`. -/
#check @totallyDisconnectedSpace_iff_connectedComponent_singleton
