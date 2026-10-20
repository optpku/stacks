/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.AssociatedCartier
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Cartier divisors that are differences of effective Cartier divisors

This file defines the representability predicate for differences of effective Cartier divisors
and records an existence result for a Cartier divisor outside that class.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- A Cartier divisor is a difference of two effective Cartier divisors when it equals the
associated Cartier divisor of one effective Cartier divisor minus that of another. -/
def IsDifferenceOfEffectiveCartier (τ : CartierDivisor X) : Prop :=
  ∃ (D E : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D.subschemeι)
    (_ : IsEffectiveCartierDivisor E.subschemeι),
    τ = cartierDivisor_ofEffectiveCartier D - cartierDivisor_ofEffectiveCartier E

/-- A Cartier divisor is a difference of effective Cartier divisors if and only if it equals
the difference of the Cartier divisors associated to two effective Cartier divisors. -/
theorem isDifferenceOfEffectiveCartier_iff (τ : CartierDivisor X) :
    IsDifferenceOfEffectiveCartier τ ↔
      ∃ (D E : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D.subschemeι)
        (_ : IsEffectiveCartierDivisor E.subschemeι),
        τ = cartierDivisor_ofEffectiveCartier D - cartierDivisor_ofEffectiveCartier E :=
  Iff.rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

/-- There exists a Cartier divisor on a variety over a field which is not the difference of two
effective Cartier divisors. -/
@[stacks 02FB]
theorem exists_cartierDivisor_not_sub_ofEffectiveCartier :
    ∃ (k : Type u) (_ : Field k) (X : SchemeOverField k) (_ : Variety X)
      (τ : CartierDivisor X.left),
      ¬ IsDifferenceOfEffectiveCartier τ :=
  sorry

end AlgebraicGeometry
