module

public import ReasLib.Topology.Separation.Opens
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 111.6.6 (1): a topological space `X` verifies the separation axiom `T0` when any
two distinct points are separated by an open set containing exactly one of them. -/
@[stacks 027C]
#check (TopologicalSpace.t0Space_iff_exists_opens :
  ∀ (X : Type u) [TopologicalSpace X],
    T0Space X ↔ Pairwise (fun x y : X =>
      ∃ U : TopologicalSpace.Opens X, Xor (x ∈ U) (y ∈ U)))

/- Definition 111.6.6 (2): a topological space `X` is Hausdorff when any two distinct points
admit disjoint open neighbourhoods. -/
@[stacks 027C]
#check (TopologicalSpace.t2Space_iff_exists_opens :
  ∀ (X : Type u) [TopologicalSpace X],
    T2Space X ↔ Pairwise (fun x y : X =>
      ∃ U V : TopologicalSpace.Opens X, x ∈ U ∧ y ∈ V ∧ Disjoint U V))
