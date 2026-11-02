/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

universe u

/- Lemma 27.13.7: the canonical degreewise restriction kernels form the intrinsic
homogeneous coordinate ideal, and its homogeneous quotient has projective spectrum Z
as a closed subscheme of the ambient projective space. -/
@[stacks 03GL] #check (coordinateIdeal_isHomogeneous :
  ∀ {R : Type u} [CommRing R] (n : ℕ)
    (Z : (ProjectiveSpace.scheme R n).IdealSheafData),
    (coordinateIdeal n Z).IsHomogeneous (ProjectiveSpace.grading R n))

@[stacks 03GL] #check (mem_coordinateIdeal_iff_canonicalVanishes :
  ∀ {R : Type u} [CommRing R] (n : ℕ)
    (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (f : MvPolynomial (Fin (n + 1)) R),
    f ∈ coordinateIdeal n Z ↔ ∀ d : ℕ,
      canonicalDegreeMap n Z d
        (DirectSum.decompose (ProjectiveSpace.grading R n) f d) = 0)

@[stacks 03GL] #check (coordinateIdeal_quotient_isomorphic :
  ∀ {R : Type u} [CommRing R] (n : ℕ)
    (Z : (ProjectiveSpace.scheme R n).IdealSheafData),
    let I : HomogeneousIdeal (ProjectiveSpace.grading R n) :=
      { toSubmodule := coordinateIdeal n Z
        is_homogeneous' := coordinateIdeal_isHomogeneous n Z }
    letI := GradedAlgebra.Quotient.gradedAlgebra
      (ProjectiveSpace.grading R n) I.toIdeal I.isHomogeneous
    Nonempty (Over.mk (projQuotientMap (ProjectiveSpace.grading R n) I) ≅
      Over.mk Z.subschemeι))
