module

public import Mathlib.Topology.Irreducible
import StacksCheckRecall

@[expose] public section

/- Exercise 111.6.19: any irreducible subset of a topological space `X` is contained in an
irreducible component of `X`; the canonical owner is
`exists_mem_irreducibleComponents_subset_of_isIrreducible`. -/
@[stacks 02DA]
#check @exists_mem_irreducibleComponents_subset_of_isIrreducible
