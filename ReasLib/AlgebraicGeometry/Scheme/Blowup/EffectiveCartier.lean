/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.UniversalProperty
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.Sum
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Factors

/-!
# Blowups and effective Cartier divisors

Multiplying a blowup center by an effective Cartier divisor does not change the blowup
morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsBlowup

/-- A morphism that is a blowup in `I` is also a blowup in `I * D` when `D` is an effective
Cartier divisor. -/
theorem mul_effectiveCartier {S S' : Scheme.{u}} (I D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (b : S' ⟶ S) [IsBlowup b I] :
    IsBlowup b (I * D) := sorry

end AlgebraicGeometry.IsBlowup
