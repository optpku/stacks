module

public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic
public import stacks_project.Chap87.Lemma_87_5_6_CompletedRing

/-!
# Weakly adic completed tensor products

If `algebraMap B A` and `algebraMap B C` are continuous maps of linearly
topologized rings and `A`, `C` are weakly pre-adic, then the completed tensor
`Completed B A C` is weakly adic.
-/

@[expose] public section

universe u

namespace Algebra.TensorProduct.Completed

variable {B A C : Type u}
variable [CommRing B] [CommRing A] [CommRing C]
variable [Algebra B A] [Algebra B C]
variable [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]

/-- If `A` and `C` are weakly pre-adic, then `Completed B A C` is weakly adic. -/
theorem isWeaklyAdicRing [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsWeaklyPreadicRing A]
    [TopologicalRing.IsWeaklyPreadicRing C]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C)) :
    TopologicalRing.IsWeaklyAdicRing (Completed B A C) := sorry

end Algebra.TensorProduct.Completed
