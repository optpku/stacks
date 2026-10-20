module

public import Mathlib.Topology.Bases
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Mathlib's canonical owner `TopologicalSpace.IsTopologicalBasis` packages a basis through
generation and intersection properties. The exact source conditions construct this owner via
`TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`, while
`TopologicalSpace.IsTopologicalBasis.isOpen` and
`TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open` recover openness and pointwise
refinement. Direct use therefore preserves the textbook definition in both directions and gives
downstream files the established basis API without a parallel local predicate or wrapper theorem.
-/

/- Definition 5.5.1: a collection of subsets of a topological space is a basis for the topology
if every basis element is open and every open set is locally refined by a basis element; this is
the canonical mathlib predicate `TopologicalSpace.IsTopologicalBasis`. -/
@[stacks 004P "topological basis via openness and pointwise refinement"]
#check TopologicalSpace.IsTopologicalBasis
