/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Divisor sums as scheme-theoretic unions

This file identifies a sum of effective Cartier divisors with their scheme-theoretic union
under the effective-intersection hypothesis.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- If the pullback of `D` to `D'` is an effective Cartier divisor, then the divisor sum is
cut out by the intersection of the two ideal sheaves. -/
@[stacks 0C4R]
theorem sum_eq_inf_of_comap
    {X : Scheme.{u}} (D D' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor D'.subschemeι]
    [IsEffectiveCartierDivisor (D.comap D'.subschemeι).subschemeι] :
    effectiveCartierDivisorSum D D' = D ⊓ D' := sorry

/-- Under the same hypotheses, the closed subscheme underlying the divisor sum is the
scheme-theoretic union of the two divisors. -/
theorem subscheme_sum_eq_union_of_comap
    {X : Scheme.{u}} (D D' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor D'.subschemeι]
    [IsEffectiveCartierDivisor (D.comap D'.subschemeι).subschemeι] :
    (effectiveCartierDivisorSum D D').subscheme = Scheme.schemeTheoreticUnion D D' := by
  rw [sum_eq_inf_of_comap]

end AlgebraicGeometry.Scheme.IdealSheafData
