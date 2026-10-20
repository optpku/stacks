module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata

/-!
# Empty fibers of relative normalizations over Nagata schemes

This module records a discrete-valuation criterion for a one-dimensional stalk of a relative
normalization when the source has empty fiber over the point.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A one-dimensional stalk of the relative normalization of a reduced finite-type scheme over a
Nagata scheme admits compatible integral-domain and discrete-valuation-ring structures when the
source has empty fiber over the point. -/
theorem isDiscreteValuationRing_stalk_normalization_of_empty_fiber
    {Y X : Scheme.{u}} (f : Y ⟶ X) [FiniteType f] [IsReduced Y] [Scheme.Nagata X]
    (x' : f.normalization)
    (hdim : ringKrullDim (f.normalization.presheaf.stalk x') = 1)
    (hfiber : IsEmpty (f.toNormalization.fiber x')) :
    ∃ (_ : IsDomain (f.normalization.presheaf.stalk x')),
      IsDiscreteValuationRing (f.normalization.presheaf.stalk x') := sorry

end AlgebraicGeometry.Scheme.Hom
