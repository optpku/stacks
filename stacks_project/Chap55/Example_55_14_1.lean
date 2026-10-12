/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NodalModel.Power.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.NodalModel

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) [Fact (Irreducible π)]

/- Example 55.14.1 (1): the exponent-zero nodal model is smooth over `Spec R`. -/
@[stacks 0CDC] #check (AlgebraicGeometry.NodalModel.Power.instSmoothToBaseZero π :
  Smooth (Power.toBase π 0))

variable (n : ℕ)

/- Example 55.14.1 (2): every nodal model `xy = π ^ n` is at worst nodal of relative
 dimension one over `Spec R`. -/
@[stacks 0CDC] #check (AlgebraicGeometry.NodalModel.Power.instAtWorstNodalToBase π n :
  AtWorstNodal (Power.toBase π n))

/- Example 55.14.1 (3): the exponent-one nodal model is regular. -/
@[stacks 0CDC] #check (AlgebraicGeometry.NodalModel.Power.instRegularSpectrumOne π :
  Scheme.Regular (Power.spectrum R π 1))

/- Example 55.14.1 (4): for exponent greater than one, `x` and `y` do not generate the
 distinguished maximal ideal `(π, x, y)`. -/
@[stacks 0CDC] #check (AlgebraicGeometry.NodalModel.Power.span_xy_ne_closedPointIdeal π n :
  1 < n → Ideal.span {Power.x π n, Power.y π n} ≠ Power.closedPointIdeal π n)

/- Example 55.14.1 (5): a nodal model of exponent greater than one is not regular. -/
@[stacks 0CDC] #check (AlgebraicGeometry.NodalModel.Power.notRegularSpectrum_of_one_lt π n :
  1 < n → ¬ Scheme.Regular (Power.spectrum R π n))

/- Example 55.14.1 (6): after `n / 2` successive blowups at singular closed points, the
 terminal model is regular and remains at worst nodal over `Spec R`. -/
@[stacks 0CDC] #check (AlgebraicGeometry.NodalModel.Power.existsRegularResolution π n :
  ∃ (Y : Scheme.{u}) (s : Scheme.SingularPointBlowupSequence (Power.spectrum R π n) Y),
    s.length = n / 2 ∧ Scheme.Regular Y ∧ AtWorstNodal (s.toSource ≫ Power.toBase π n))

end AlgebraicGeometry.NodalModel
