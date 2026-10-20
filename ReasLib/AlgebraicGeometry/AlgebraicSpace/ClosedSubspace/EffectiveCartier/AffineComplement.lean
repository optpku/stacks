module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Effective Cartier complements of dense affine opens

The reduced complement of a dense affine open in a regular Noetherian
absolutely separated algebraic space is an effective Cartier divisor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- The reduced induced closed subspace on the complement of a dense affine open
in a regular Noetherian absolutely separated algebraic space is an effective
Cartier divisor. -/
theorem isEffectiveCartierDivisor_reducedCompl
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsRegular X] [IsNoetherian X] [IsAbsolutelySeparated X]
    (U : OpenSubspace X) [IsAffine U.X] (hU : Dense U.pointsSet) :
    IsEffectiveCartierDivisor U.reducedComplement.ι :=
  sorry

/-- A dense affine open in a regular Noetherian absolutely separated algebraic
space is the complement of an effective Cartier divisor. -/
theorem exists_effectiveCartierDivisor_of_isSeparated
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsRegular X] [IsNoetherian X] [IsAbsolutelySeparated X]
    (U : OpenSubspace X) [IsAffine U.X] (hU : Dense U.pointsSet) :
    ∃ D : ClosedSubspace X,
      IsEffectiveCartierDivisor D.ι ∧ U.pointsSet = D.pointsSetᶜ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
