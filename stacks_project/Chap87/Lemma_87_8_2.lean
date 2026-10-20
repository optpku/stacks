module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Descent
import StacksCheckRecall

/-!
# Lemma 87.8.2

Weak pre-admissibility descends along a continuous taut homomorphism of linearly
topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

open RingHom

/- Lemma 87.8.2: In the situation above, if `B` is weakly pre-admissible, then `A`
is weakly pre-admissible. The situation is a continuous taut homomorphism
`φ : A →+* B` of linearly topologized rings such that `φ.FaithfullyFlatOpenQuotients`:
for every open ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`,
the induced map `A ⧸ I →+* B ⧸ J` is faithfully flat. -/
@[stacks 0GXM] #check (TopologicalRing.IsWeaklyPreadmissibleRing.of_isTaut :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyPreadmissibleRing B]
    {φ : A →+* B},
    Continuous φ → φ.IsTaut → φ.FaithfullyFlatOpenQuotients →
      TopologicalRing.IsWeaklyPreadmissibleRing A)

#check (TopologicalRing.IsWeaklyPreadmissibleRing.isWeakIdealOfDefinition_of :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyPreadmissibleRing B]
    {φ : A →+* B},
    Continuous φ → φ.IsTaut → φ.FaithfullyFlatOpenQuotients →
    ∀ {J : Ideal B}, TopologicalRing.Ideal.IsWeakIdealOfDefinition J →
    ∀ {I : Ideal A}, IsOpen (I : Set A) → Ideal.map φ I ≤ J →
      TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
