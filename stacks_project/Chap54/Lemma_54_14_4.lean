module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.CompleteLocal

@[expose] public section

universe u

/- Lemma 54.14.4: the spectrum of a two-dimensional Noetherian complete normal local ring
admits a resolution of singularities. -/
@[stacks 0BGN] #check
  (AlgebraicGeometry.Scheme.existsResolution_of_completeNormalLocalDomain :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNormalRing A]
    (h_dimension : ringKrullDim A = 2),
    ∃ (X : AlgebraicGeometry.Scheme.{u})
      (f : X ⟶ AlgebraicGeometry.Spec (.of A)),
      AlgebraicGeometry.IsResolution f)
