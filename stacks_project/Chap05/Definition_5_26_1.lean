module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCheckRecall

@[expose] public section

/- Definition 5.26.1: a topological space is extremally disconnected if the closure of every open
subset is open; this is the canonical mathlib predicate `ExtremallyDisconnected`. -/
@[stacks 08YI "extremally disconnected spaces"]
#check ExtremallyDisconnected
