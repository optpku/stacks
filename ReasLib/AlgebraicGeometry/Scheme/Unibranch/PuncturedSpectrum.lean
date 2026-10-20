module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.RingTheory.LocalRing.Unibranch.StrictHenselization

/-!
# Geometric unibranchness and punctured spectra

This file relates geometric unibranchness of a Noetherian scheme to connectedness of punctured
spectra of strict Henselizations of its local rings away from generic points.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A Noetherian scheme is geometrically unibranch exactly when the punctured spectrum of every
strict Henselization of each stalk away from the generic points is connected. -/
theorem isGeometricallyUnibranch_iff_connectedSpace_puncturedSpectrum [IsNoetherian X] :
    X.isGeometricallyUnibranch ↔
      ∀ x : X,
        x ∉ genericPoints X →
          ∀ (Ash : Type u) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
            [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
              ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme Ash) := sorry

end AlgebraicGeometry.Scheme
