/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.Blowup

/-!
# Compatibility names for the Rees-Proj blowup API
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.ReesProj

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- The source-facing grading name for the canonical Rees grading. -/
abbrev grading (I : Ideal A) := ReesAlgebra.Grading.grade I

#check (ReesAlgebra.Grading.grade I : ℕ → Submodule A (reesAlgebra I))
#check (AlgebraicGeometry.ReesProj.toSpec I :
  Proj (ReesAlgebra.Grading.grade I) ⟶ Spec (.of A))

end AlgebraicGeometry.ReesProj
