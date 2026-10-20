module

public import ReasLib.RingTheory.Catenary.Equidimensional
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.3.2: the prime spectrum of a Noetherian catenary local ring satisfying Serre's
condition `(S₂)` is equidimensional. -/
@[stacks 0FIW] #check (SerreConditionS.instEquidimensionalSpacePrimeSpectrum :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsCatenaryRing A] [SerreConditionS A 2],
    TopologicalSpace.EquidimensionalSpace (PrimeSpectrum A))
