module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal

@[expose] public section

open AlgebraicGeometry Order

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/-- The order-of-vanishing function of a function-field unit has locally finite support. -/
theorem locallyFiniteSupport_ord (f : X.functionFieldˣ) :
    LocallyFiniteSupport (fun x : X ↦ X.ord f x) := sorry

/-- The principal algebraic cycle associated to a function-field unit. -/
noncomputable def principal (f : X.functionFieldˣ) : AlgebraicCycle X ℤ :=
  ⟨fun x ↦ X.ord f x, Set.subset_univ _, fun x _ ↦ locallyFiniteSupport_ord X f x⟩

/-- The coefficient of a principal algebraic cycle is the corresponding order of vanishing. -/
theorem principal_apply (f : X.functionFieldˣ) (x : X) :
    principal X f x = X.ord f x := sorry

/-- A principal algebraic cycle vanishes away from points of codimension one. -/
theorem principal_apply_eq_zero_of_coheight_ne_one
    (f : X.functionFieldˣ) (x : X) (hx : coheight x ≠ 1) :
    principal X f x = 0 := sorry

/-- At the generic point of a prime divisor, the principal-cycle coefficient agrees with the
coefficient of the corresponding principal Weil divisor. -/
theorem principal_apply_primeDivisor (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principal X f Z.genericPoint = (X.principalWeilDivisor f).coeff Z := sorry

end AlgebraicGeometry.AlgebraicCycle
