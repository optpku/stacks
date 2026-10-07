module

public import ReasLib.Topology.KrullDimension.Equidimensional
import StacksCheckRecall

@[expose] public section

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.10.5: equidimensionality means that all irreducible components have the same
topological Krull dimension. -/
@[stacks 0058]
#check (EquidimensionalSpace : ∀ X : Type u, [TopologicalSpace X] → Prop)
