module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative effective Cartier divisors

This file owns effective Cartier divisors on a scheme over a base whose structural morphism to
the base is flat.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A divisor datum `D` on `X` is relatively effective Cartier over `f : X ⟶ S` when it is an
effective Cartier divisor and the induced morphism from its subscheme to `S` is flat. -/
@[stacks 062T, mk_iff]
class IsRelativeEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) (D : X.IdealSheafData) : Prop
    extends IsEffectiveCartierDivisor D.subschemeι, Flat (D.subschemeι ≫ f)

end AlgebraicGeometry
