module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement

/-!
# Scheme-theoretic density of effective Cartier divisor complements

The open complement of an effective Cartier divisor on an algebraic space is
scheme-theoretically dense in the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor

/-- The inclusion of the open complement of an effective Cartier divisor on an
algebraic space is scheme-theoretically dense. -/
instance schemeTheoreticallyDense_closedImmersionComplementι
    {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] :
    IsSchemeTheoreticallyDense (closedImmersionComplementι i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor
