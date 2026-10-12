/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Topology
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification.AffineOpenCover
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineStratification

/-!
# Affine stratifications of standard projective space

This file determines the affine stratification number of standard projective space over a field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineStratification

/-- The affine stratification number of standard projective `n`-space over a field is `n`. -/
theorem number_projectiveSpace_eq (k : Type u) [Field k] (n : ℕ) :
    number (ProjectiveSpace.scheme k n) = n := sorry

end AlgebraicGeometry.Scheme.FiniteAffineStratification
