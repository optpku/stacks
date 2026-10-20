module

public import ReasLib.Topology.Algebra.TensorProduct.CompletedRing.Ideal
import StacksCheckRecall

/-!
# Lemma 87.4.11

The topological closure of an extended ideal `IB` is the kernel of the canonical
map from `B` into the completed tensor product of `B` with `A ⧸ I` over `A`.
-/

@[expose] public section

universe u

open Algebra.TensorProduct

/- Lemma 87.4.11: If `algebraMap A B` is a continuous map of linearly topologized rings
and `I` is an ideal of `A`, then the topological closure of `I.map (algebraMap A B)`
equals the kernel of `Completed.includeLeft A B (A ⧸ I)`. -/
@[stacks 0AMZ] #check (Ideal.closure_map_eq_ker_includeLeft :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsLinearTopology A A] [IsLinearTopology B B] [Algebra A B]
    (hφ : Continuous (algebraMap A B)) (I : Ideal A),
    (I.map (algebraMap A B)).closure = RingHom.ker (Completed.includeLeft A B (A ⧸ I)))

/- Membership in the topological closure of the extended ideal `I.map (algebraMap A B)`
is equivalent to vanishing under `Completed.includeLeft A B (A ⧸ I)`. -/
#check (Ideal.mem_closure_map_iff_includeLeft_eq_zero :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsLinearTopology A A] [IsLinearTopology B B] [Algebra A B]
    (hφ : Continuous (algebraMap A B)) (I : Ideal A) {b : B},
    b ∈ (I.map (algebraMap A B)).closure ↔
      Completed.includeLeft A B (A ⧸ I) b = 0)
