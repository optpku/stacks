module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Completion
import StacksCheckRecall

@[expose] public section

open scoped ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 52.27.4: for a Noetherian local ring of depth at least two, pullback from its
punctured spectrum to the punctured spectrum of its maximal-ideal completion is injective
on Picard groups. -/
@[stacks 0F2G] #check
  (AlgebraicGeometry.PuncturedSpectrum.completionMap_picardPullback_injective :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (_hdepth : (2 : ℕ∞) ≤ moduleDepth A A),
      Function.Injective
        (Scheme.Hom.picardPullback
          (AlgebraicGeometry.PuncturedSpectrum.completionMap A)))

end AlgebraicGeometry.PuncturedSpectrum
