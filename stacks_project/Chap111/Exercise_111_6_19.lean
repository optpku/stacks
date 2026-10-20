module

public import ReasLib.Topology.IrreducibleComponents.Containment
import StacksCheckRecall

@[expose] public section

/- Exercise 111.6.19: any irreducible subset of a topological space `X` is contained in an
irreducible component of `X`. -/
@[stacks 02DA]
#check (TopologicalSpace.exists_mem_irreducibleComponents_subset_of_isIrreducible :
  ∀ {X : Type*} [TopologicalSpace X] (s : Set X), IsIrreducible s →
    ∃ u ∈ irreducibleComponents X, s ⊆ u)
