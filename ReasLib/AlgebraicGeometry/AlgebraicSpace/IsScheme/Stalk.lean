module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints

/-!
# Scheme recognition from stalkwise base changes

A quasi-compact quasi-separated algebraic space over a scheme is a scheme if
its base change to the spectrum of the base stalk at the image of each point
is a scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over a scheme with quasi-compact quasi-separated
structural morphism is a scheme if its base change to the spectrum of the
base stalk at the image of each of its points is a scheme. -/
theorem isScheme_of_forall_isScheme_baseChange_fromSpecStalk
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [QuasiCompact (SchemeRealization.toBase X)]
    [QuasiSeparated (SchemeRealization.toBase X)]
    (h_fromSpecStalk : ∀ x : Points X,
      IsScheme (baseChange (S.fromSpecStalk (Points.base x)) X)) :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
