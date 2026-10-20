module

public import ReasLib.Topology.KrullDimension.Local
import StacksCheckRecall

@[expose] public section

universe u

open TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.10.1 (1): chains of irreducible closed subsets are strict series in the canonical
poset of irreducible closed subsets. -/
@[stacks 0055 "chains as strict series of irreducible closed subsets"]
#check (LTSeries (IrreducibleCloseds X))

/- Definition 5.10.1 (2): the length of a chain is its canonical terminal index. -/
@[stacks 0055 "length as the terminal index of a strict series"]
#check fun p : LTSeries (IrreducibleCloseds X) ↦ p.length

/- Definition 5.10.1 (3): the Krull dimension of a topological space is the supremum of lengths
of strict chains of irreducible closed subsets. -/
@[stacks 0055 "global Krull dimension from irreducible closed chains"]
#check (topologicalKrullDim X : WithBot ℕ∞)

/- Definition 5.10.1 (4): the Krull dimension of `X` at a point `x` is the minimum of the Krull
dimensions of the open neighbourhoods of `x`. -/
@[stacks 0055 "local Krull dimension at a point"]
#check (topologicalKrullDimAt : X → WithBot ℕ∞)
