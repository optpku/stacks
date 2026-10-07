module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Weil

/-!
# Orders of vanishing along prime divisors

This file connects a prime divisor to its generic-point stalk and the corresponding valuation of
a rational function.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The generic local ring attached to a prime divisor. -/
noncomputable abbrev PrimeDivisor.genericPointStalk (Z : PrimeDivisor X) :=
  X.presheaf.stalk Z.genericPoint

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/-- The order of a rational function along a prime divisor is its valuation in the generic-point
stalk. -/
noncomputable abbrev primeDivisorOrder
    (Z : PrimeDivisor X) (f : X.functionFieldˣ) : ℤ :=
  X.ord (f : X.functionField) Z.genericPoint

end AlgebraicGeometry.Scheme
