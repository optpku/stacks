/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NodalModel.Power
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.SingularPointSequence


@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.NodalModel.Power

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) [Fact (Irreducible π)]

/-- the exponent-zero nodal model is smooth over `Spec R`. -/
instance instSmoothToBaseZero : Smooth (toBase π 0) := sorry

/-- every nodal model `xy = π ^ n` is at worst nodal of relative
dimension one over `Spec R`. -/
instance instAtWorstNodalToBase (n : ℕ) : AtWorstNodal (toBase π n) := sorry

/-- the exponent-one nodal model is regular. -/
instance instRegularSpectrumOne : Scheme.Regular (spectrum R π 1) := sorry

/-- for exponent greater than one, `x` and `y` do not generate the
distinguished maximal ideal `(π, x, y)`. -/
theorem span_xy_ne_closedPointIdeal (n : ℕ) (h_one : 1 < n) :
    Ideal.span {x π n, y π n} ≠ closedPointIdeal π n := sorry

/-- a nodal model of exponent greater than one is not regular. -/
theorem notRegularSpectrum_of_one_lt (n : ℕ) (h_one : 1 < n) :
    ¬ Scheme.Regular (spectrum R π n) := sorry

/-- after `n / 2` successive blowups at singular closed points, the
terminal model is regular and remains at worst nodal over `Spec R`. -/
theorem existsRegularResolution (n : ℕ) :
    ∃ (Y : Scheme.{u})
      (s : Scheme.SingularPointBlowupSequence (spectrum R π n) Y),
      s.length = n / 2 ∧ Scheme.Regular Y ∧ AtWorstNodal (s.toSource ≫ toBase π n) := sorry

end AlgebraicGeometry.NodalModel.Power
