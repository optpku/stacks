module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 40.14.9: the shared theorem implies the source statement; it is stronger because
the quasi-compactness hypothesis on the immersion is unnecessary. -/
@[stacks 0ABH] #check
  (AlgebraicGeometry.Scheme.isAffine_of_basicOpen_preimage_of_isClosed :
    ∀ {A : CommRingCat.{u}} {V : Scheme.{u}} (j : V ⟶ Spec A) [IsImmersion j] (f : A),
      IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen f) →
        IsClosed (Set.range j ∩ PrimeSpectrum.zeroLocus ({f} : Set A)) → IsAffine V)

end AlgebraicGeometry.Scheme
