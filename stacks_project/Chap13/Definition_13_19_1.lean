/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution
import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
import StacksCheckRecall

@[expose] public section

universe u v

variable {𝒜 : Type u} [CategoryTheory.Category.{v} 𝒜] [CategoryTheory.Abelian 𝒜]
variable (A : 𝒜) (K : CochainComplex 𝒜 ℤ)

/- Definition 13.19.1 (1): a projective resolution of an object A is a
nonpositive cochain complex of projective objects with a quasi-isomorphism to A[0].
These conditions express the four object-resolution conditions: the degree-zero
augmentation identifies the cokernel of d⁻¹ with A, and negative cohomology vanishes. -/
@[stacks 0644] #check
  (CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom (CategoryTheory.isProjective 𝒜) 0
    ((CochainComplex.singleFunctor 𝒜 0).obj A) : Type (max u v))

/- Definition 13.19.1 (2): a projective resolution of a complex K is a
bounded-above complex of projective objects with a quasi-isomorphism to K. -/
@[stacks 0644] #check (CochainComplex.ProjectiveResolution K : Type (max u v))
