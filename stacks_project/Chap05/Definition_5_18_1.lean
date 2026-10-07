module

public import Mathlib.Topology.JacobsonSpace
import StacksCheckRecall

@[expose] public section

/- Definition 5.18.1: a topological space `X` is Jacobson when every closed subset `Z` is the
closure of `Z ∩ closedPoints X`; this is exactly the canonical mathlib class `JacobsonSpace`. -/
@[stacks 005U "closed subsets are determined by their closed points"]
#check JacobsonSpace
