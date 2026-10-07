module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.CompleteIntersection.Local
public import stacks_project.Chap58.Lemma_58_21_6_Purity

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- Proposition 58.25.3: if `A` is a Noetherian local complete-intersection ring of
Krull dimension at least `3`, then purity holds for `A`, i.e. every finite étale
cover of the punctured spectrum `U = Spec A \ {m}` extends over `Spec A`. -/
@[stacks 0BPD, instance]
instance hasPurity_of_completeIntersectionLocalRing
    {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]
    [Fact (3 ≤ ringKrullDim A)] :
    HasPurity A := sorry

/-- Finite étale covers of the punctured spectrum of a complete-intersection local
ring of Krull dimension at least `3` extend over the spectrum. -/
theorem finiteEtale_extends_of_completeIntersectionLocalRing
    {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]
    [Fact (3 ≤ ringKrullDim A)] :
    ∀ V : Scheme.FiniteEtale (scheme A),
      ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
        Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V) := sorry

end AlgebraicGeometry.PuncturedSpectrum
