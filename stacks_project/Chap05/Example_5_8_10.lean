module

public import ReasLib.Topology.Cofinite.Basic
public import ReasLib.Topology.Sober.Subsingleton
import StacksCheckRecall

@[expose] public section

universe u

variable {Y : Type u} [Infinite Y]

/-!
# Example 5.8.10

`CofiniteTopology` and its `T1Space` instance are Mathlib's owners for the
ambient topology.  ReasLib adds only the genuinely missing non-quasi-sober
theorem; the singleton clauses are consequences of Mathlib's canonical
singleton API and the reusable `Subsingleton.sober` bridge.
-/

/- Example 5.8.10 (1): the cofinite topology on an infinite set is Kolmogorov. -/
@[stacks 0B33 "the infinite cofinite space is Kolmogorov"]
#check (inferInstance : T0Space (CofiniteTopology Y))

/- Example 5.8.10 (2): the cofinite topology on an infinite set is not quasi-sober. -/
@[stacks 0B33 "the infinite cofinite space is not quasi-sober"]
#check @CofiniteTopology.not_quasiSober

/- Example 5.8.10 (3): singleton subsets cover the cofinite space. -/
@[stacks 0B33 "singleton subsets cover the cofinite space"]
#check @Set.iUnion_of_singleton

/- Example 5.8.10 (4): singleton subspaces of the cofinite space are discrete. -/
@[stacks 0B33 "singleton subspaces of the cofinite space are discrete"]
#check @Subsingleton.discreteTopology

/- Example 5.8.10 (5): singleton subspaces of the cofinite space are sober. -/
@[stacks 0B33 "singleton subspaces of the cofinite space are sober"]
#check @Subsingleton.sober
