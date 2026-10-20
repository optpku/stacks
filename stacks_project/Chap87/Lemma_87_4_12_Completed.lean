module

public import ReasLib.Topology.Algebra.TensorProduct.Admissibility
import StacksCheckRecall

@[expose] public section

open Algebra.TensorProduct

universe u

/- Lemma 87.4.12 (1): The completed tensor product of weakly pre-admissible
linearly topologized rings over a linearly topologized base is weakly admissible
when both algebra maps are continuous. -/
@[stacks 0GB4] #check (Algebra.TensorProduct.Completed.isWeaklyAdmissibleRing :
  ∀ {B A C : Type u} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
    [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsWeaklyPreadmissibleRing A]
    [TopologicalRing.IsWeaklyPreadmissibleRing C]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C)),
    TopologicalRing.IsWeaklyAdmissibleRing (Completed B A C))
