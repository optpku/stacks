/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of relative effective Cartier divisors

This file establishes the stability of relative effective Cartier divisors under arbitrary base
change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IsRelativeEffectiveCartierDivisor

/-- The pullback of a relative effective Cartier divisor is an effective Cartier divisor. -/
@[stacks 056Q]
theorem isEffectiveCartierDivisor_comap_pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D] :
    IsEffectiveCartierDivisor (D.comap (pullback.fst f g)).subschemeι := sorry

/-- After base change, the pulled-back divisor is relative effective Cartier over the new base. -/
instance comap_pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D] :
    IsRelativeEffectiveCartierDivisor (pullback.snd f g) (D.comap (pullback.fst f g)) := sorry

end AlgebraicGeometry.IsRelativeEffectiveCartierDivisor
