module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic

/-!
# Lemma 87.7.5

Weakly pre-adic rings ascend along continuous taut homomorphisms of linearly
topologized rings.
-/

@[expose] public section

universe u v

open RingHom

namespace TopologicalRing.Ideal

/-- If `φ` is a continuous taut homomorphism and `I` is weakly adic in the source,
then `Ideal.map φ I` is weakly adic in the target. -/
theorem IsWeaklyAdic.map_of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : IsWeaklyAdic I) : IsWeaklyAdic (Ideal.map φ I) :=
  sorry

end TopologicalRing.Ideal

namespace TopologicalRing.IsWeaklyPreadicRing

/-- Lemma 87.7.5: Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and `A` is weakly pre-adic, then `B` is
weakly pre-adic. -/
@[stacks 0GXI]
theorem of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsWeaklyPreadicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    IsWeaklyPreadicRing B :=
  sorry

end TopologicalRing.IsWeaklyPreadicRing
