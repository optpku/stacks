/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_49_3_Associated
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety
import Mathlib.Tactic.CrossRefAttribute

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

/-- Unfold `IsDifferenceOfEffectiveCartier` as equality with a difference of associated
Cartier divisors of effective Cartier divisors. -/
theorem isDifferenceOfEffectiveCartier_iff (τ : CartierDivisor X) :
    IsDifferenceOfEffectiveCartier τ ↔
      ∃ (D E : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D.subschemeι)
        (_ : IsEffectiveCartierDivisor E.subschemeι),
        τ = cartierDivisor_ofEffectiveCartier D - cartierDivisor_ofEffectiveCartier E :=
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

/-- Exercise 111.49.8: there exists a Cartier divisor on a variety over a field which is not
the difference of two effective Cartier divisors. -/
@[stacks 02FB]
theorem exists_cartierDivisor_not_sub_ofEffectiveCartier :
    ∃ (k : Type u) (_ : Field k) (X : SchemeOverField k) (_ : Variety X)
      (_ : HasSheafify (Opens.grothendieckTopology X.left.toTopCat) AddCommGrpCat.{u})
      (_ : (Opens.grothendieckTopology X.left.toTopCat).HasSheafCompose
        (CategoryTheory.forget CommRingCat.{u}))
      (τ : CartierDivisor X.left),
      ¬ IsDifferenceOfEffectiveCartier τ :=
  sorry

end AlgebraicGeometry
