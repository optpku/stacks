module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal.Complement
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure

/-!
# Complements of effective Cartier divisors

This file records affineness and scheme-theoretic density of the open complement of an effective
Cartier divisor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.IsEffectiveCartierDivisor

/-- The inclusion of the open complement of an effective Cartier divisor is affine. -/
theorem isAffineHom_closedImmersionComplement {S D : Scheme.{u}} (i : D ⟶ S)
    [AlgebraicGeometry.IsEffectiveCartierDivisor i] :
    IsAffineHom (closedImmersionComplement i).ι := sorry

/-- The open complement of an effective Cartier divisor is scheme-theoretically dense. -/
theorem schemeTheoreticallyDense_closedImmersionComplement {S D : Scheme.{u}} (i : D ⟶ S)
    [AlgebraicGeometry.IsEffectiveCartierDivisor i] :
    schemeTheoreticallyDense (closedImmersionComplement i) := sorry

end AlgebraicGeometry.IsEffectiveCartierDivisor
