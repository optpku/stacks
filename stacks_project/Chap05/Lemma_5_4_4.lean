module

public import Mathlib.Topology.SeparatedMap
import StacksCheckRecall

@[expose] public section

/- Canonical core: fiberwise separation is preserved by pullback without continuity assumptions. -/
@[stacks 0CY4 "separatedness is preserved by pullback"]
#check IsSeparatedMap.pullback
