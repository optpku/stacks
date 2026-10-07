module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch.PuncturedSpectrum

open AlgebraicGeometry

universe u

/- Lemma 28.15.3: for a Noetherian scheme `X`, being geometrically unibranch is equivalent to
connectedness of the punctured spectrum of every strict Henselization of a stalk away from the
generic points of `X`. -/
@[stacks 0BQ4] #check
  (AlgebraicGeometry.Scheme.isGeometricallyUnibranch_iff_connectedSpace_puncturedSpectrum :
    ∀ (X : Scheme.{u}) [IsNoetherian X],
      X.isGeometricallyUnibranch ↔
        ∀ x : X,
          x ∉ genericPoints X →
            ∀ (Ash : Type u) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
              [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
                ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme Ash))
