module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.Topology.ClosedPoints

/-!
# Punctured spectra without closed points

The specialization-chain criterion is separated from the existence theorem,
so other examples can reuse the same topological argument.
-/

@[expose] public section

open AlgebraicGeometry PrimeSpectrum IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- If every punctured-spectrum point has a distinct specialization in the punctured spectrum,
then the punctured spectrum has no closed points. -/
@[stacks 01IY "punctured spectrum specialization criterion"]
theorem closedPoints_scheme_eq_empty_of_specializes
    (hchain : ∀ p : PrimeSpectrum R, p ≠ closedPoint R →
      ∃ q : PrimeSpectrum R, q ≠ closedPoint R ∧ p ≠ q ∧ p ⤳ q) :
    closedPoints (scheme R) = ∅ := sorry

/-- In every universe there exists a nonempty scheme with no closed points. -/
@[stacks 01IY]
theorem exists_nonempty_scheme_without_closed_points :
    ∃ X : Scheme.{u}, Nonempty X ∧ closedPoints X = ∅ := sorry

end AlgebraicGeometry.PuncturedSpectrum
