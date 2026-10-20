module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SerreCondition
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.SerreCondition.Normal

/-!
# Effective Cartier divisors on normal locally Noetherian algebraic spaces

An effective Cartier divisor on a locally Noetherian normal algebraic space
satisfies Serre's condition `(S₁)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An effective Cartier divisor on a locally Noetherian normal algebraic space
satisfies Serre's condition `(S₁)`. -/
theorem IsEffectiveCartierDivisor.satisfiesSerreConditionS_one
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsNormal X]
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    satisfiesSerreConditionS D.X 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
