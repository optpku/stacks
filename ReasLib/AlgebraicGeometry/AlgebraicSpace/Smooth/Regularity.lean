module

public import Mathlib.Algebra.Field.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Regularity of algebraic spaces smooth over fields

An algebraic space smooth over a field is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space smooth over a field is regular. -/
instance isRegular_of_smooth_over_field {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Smooth (SchemeRealization.toBase X)] : IsRegular X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
