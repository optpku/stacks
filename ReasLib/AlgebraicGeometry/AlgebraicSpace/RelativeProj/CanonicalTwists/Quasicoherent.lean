/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Algebra

/-! # Quasi-coherence of the canonical integer-graded twist algebra -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)

/-- Every integer-degree canonical twist on relative Proj is quasi-coherent. -/
theorem CanonicalTwists.obj_isQuasicoherent (n : ℤ) :
    (CanonicalTwists.obj F hF n).IsQuasicoherent := sorry

/-- The canonical integer-graded algebra of twists on relative Proj is quasi-coherent. -/
theorem algebra_isQuasicoherent :
    (CanonicalTwists.algebra F hF).IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
