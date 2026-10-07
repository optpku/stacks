module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_8_3_OpenQuotient

/-!
# Lemma 87.8.2

Weak pre-admissibility descends along a continuous taut homomorphism of linearly
topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

open RingHom

namespace TopologicalRing.IsWeaklyPreadmissibleRing

/-- Lemma 87.8.2: In the situation above, if `B` is weakly pre-admissible, then `A`
is weakly pre-admissible. The situation is a continuous taut homomorphism
`φ : A →+* B` of linearly topologized rings such that `φ.FaithfullyFlatOpenQuotients`:
for every open ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`,
the induced map `A ⧸ I →+* B ⧸ J` is faithfully flat. -/
@[stacks 0GXM]
theorem of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients) :
    IsWeaklyPreadmissibleRing A :=
  sorry

/-- If `J` is a weak ideal of definition of `B` and `I` is an open ideal of `A` with
`Ideal.map φ I ≤ J`, then `I` is a weak ideal of definition of `A`. -/
theorem isWeakIdealOfDefinition_of {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    {J : Ideal B} (hJ : TopologicalRing.Ideal.IsWeakIdealOfDefinition J) {I : Ideal A}
    (hI : IsOpen (I : Set A)) (hmap : Ideal.map φ I ≤ J) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition I :=
  sorry

end TopologicalRing.IsWeaklyPreadmissibleRing
