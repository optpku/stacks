/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.SpreadingOut
public import ReasLib.RingTheory.Localization.Away.InjectiveAtPrime

@[expose] public section

/-!
# Germ-Injective Schemes

Sufficient conditions for a scheme to possess affine neighborhoods with injective germ maps.
-/

universe u

namespace AlgebraicGeometry

/-- A reduced scheme with finitely many irreducible components is germ-injective. -/
@[stacks 0BX3]
theorem Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents
    (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)] :
    X.IsGermInjective := sorry

/-- Germ injectivity is inferred for a reduced scheme with finitely many irreducible
components. -/
instance (priority := 100) instIsGermInjectiveOfIsReducedOfFiniteIrreducibleComponents
    {X : Scheme.{u}} [IsReduced X] [Finite (irreducibleComponents X)] :
    X.IsGermInjective :=
  Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents X

end AlgebraicGeometry
