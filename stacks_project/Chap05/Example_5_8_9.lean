module

public import ReasLib.Topology.Indiscrete
import StacksCheckRecall

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

section

variable [IndiscreteTopology X]

/-!
# Example 5.8.9

The canonical ReasLib instance `IndiscreteTopology.r1Space` supplies
quasi-sobriety through Mathlib's `R1Space.quasiSober`.  The source's singleton
cover is already split into Mathlib's set-theoretic cover identity and its
subsingleton discrete-topology instance.
-/

/- Example 5.8.9 (1): every indiscrete space is quasi-sober. -/
@[stacks 0B32 "nontrivial indiscrete spaces are quasi-sober"]
#check (inferInstance : QuasiSober X)

/- Example 5.8.9 (2): a nontrivial indiscrete space is not Kolmogorov. -/
@[stacks 0B32 "nontrivial indiscrete spaces are not Kolmogorov"]
#check @IndiscreteTopology.not_t0

/- Example 5.8.9 (3): singleton subspaces cover the space. -/
@[stacks 0B32 "singletons cover by discrete and hence Kolmogorov subspaces"]
#check @Set.iUnion_of_singleton

/- Example 5.8.9 (3): singleton subspaces are discrete. -/
@[stacks 0B32 "singletons cover by discrete and hence Kolmogorov subspaces"]
#check @Subsingleton.discreteTopology

end
