/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearEquivalence

/-!
# Linear equivalence of a difference to an effective Cartier divisor

The unbundled predicate that `D - E` is linearly equivalent to some effective
Cartier divisor, together with its associated-sheaf characterization.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The difference `D - E` of effective Cartier divisors is linearly equivalent to an
effective Cartier divisor when `D` is linearly equivalent to `E + F` for some
effective Cartier divisor `F`. -/
def differenceLinearlyEquivalentToEffective {X : Scheme.{u}}
    (D E : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D.subschemeι]
    [hE : IsEffectiveCartierDivisor E.subschemeι] : Prop :=
  ∃ (F : X.IdealSheafData) (hF : IsEffectiveCartierDivisor F.subschemeι),
    @linearlyEquivalent X D (effectiveCartierDivisorSum E F) hD
      (@instIsEffectiveCartierDivisorSum X E F hE hF)

/-- A difference is linearly equivalent to an effective Cartier divisor if and only if
its positive divisor is linearly equivalent to the sum of its negative divisor and
an effective Cartier divisor. -/
theorem differenceLinearlyEquivalentToEffective_iff {X : Scheme.{u}}
    (D E : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D.subschemeι]
    [hE : IsEffectiveCartierDivisor E.subschemeι] :
    differenceLinearlyEquivalentToEffective D E ↔
      ∃ (F : X.IdealSheafData) (hF : IsEffectiveCartierDivisor F.subschemeι),
        @linearlyEquivalent X D (effectiveCartierDivisorSum E F) hD
          (@instIsEffectiveCartierDivisorSum X E F hE hF) :=
  Iff.rfl

/-- The difference `D - E` is linearly equivalent to an effective Cartier divisor if
and only if `𝒪(D - E)` is isomorphic to the associated sheaf of some effective
Cartier divisor. -/
theorem differenceLinearlyEquivalentToEffective_iff_associatedSheaf {X : Scheme.{u}}
    (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] :
    differenceLinearlyEquivalentToEffective D E ↔
      ∃ (F : X.IdealSheafData) (hF : IsEffectiveCartierDivisor F.subschemeι),
        Nonempty (D.differenceSheaf E ≅ @associatedSheaf X F hF) :=
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
