/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.GradedPieces
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Cohomology of twists on standard projective space

This file identifies the cohomology modules of canonical twisting sheaves on standard projective
space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.twistingSheaf

/-- Degree-zero cohomology of the degree-`d` twisting sheaf on positive-dimensional standard
projective space is the degree-`d` homogeneous piece of the polynomial ring. -/
theorem cohomology_zero
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (d : ℤ) :
    IsIsomorphic
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec R n)
        (ProjectiveSpace.twistingSheaf R n d) 0)
      (ModuleCat.of R (ProjectiveSpace.gradedPiece R n d)) := sorry

/-- Cohomology of the degree-`d` twisting sheaf on positive-dimensional standard projective
space vanishes in every degree distinct from zero and the dimension. -/
theorem cohomology_isZero_of_ne
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (d : ℤ) (q : ℕ)
    (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec R n)
        (ProjectiveSpace.twistingSheaf R n d) q) := sorry

/-- Top-degree cohomology of the degree-`d` twisting sheaf on positive-dimensional standard
projective space is the linear dual of the homogeneous piece in degree `-n - 1 - d`. -/
theorem cohomology_top
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (d : ℤ) :
    IsIsomorphic
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec R n)
        (ProjectiveSpace.twistingSheaf R n d) n)
      (ModuleCat.of R (ProjectiveSpace.topCohomologyDual R n d)) := sorry

/-- For a nonnegative twist on standard projective space, degree-zero cohomology is the
corresponding homogeneous piece of the polynomial ring. -/
theorem cohomology_zero_of_nonneg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : 0 ≤ d) :
    IsIsomorphic
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec R n)
        (ProjectiveSpace.twistingSheaf R n d) 0)
      (ModuleCat.of R (ProjectiveSpace.gradedPiece R n d)) := sorry

/-- For a negative twist on standard projective space, top-degree cohomology is the linear dual
of the homogeneous piece in degree `-n - 1 - d`. -/
theorem cohomology_top_of_neg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : d < 0) :
    IsIsomorphic
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec R n)
        (ProjectiveSpace.twistingSheaf R n d) n)
      (ModuleCat.of R (ProjectiveSpace.topCohomologyDual R n d)) := sorry

/-- Cohomology of a twisting sheaf on standard projective space vanishes outside the
degree-zero nonnegative-twist case and the top-degree negative-twist case. -/
theorem cohomology_isZero_of_not_cases
    (R : Type u) [CommRing R] (n q : ℕ) (d : ℤ)
    (h_zero : ¬ (q = 0 ∧ 0 ≤ d)) (h_top : ¬ (q = n ∧ d < 0)) :
    IsZero
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec R n)
        (ProjectiveSpace.twistingSheaf R n d) q) := sorry

end AlgebraicGeometry.ProjectiveSpace.twistingSheaf
