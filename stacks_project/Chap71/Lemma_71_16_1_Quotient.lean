/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.ClosedSubspace

/-! # Degreewise kernels of relative-Proj closed subspaces -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)
variable {Z : AlgebraicSpace S} (i : Z ⟶ toAlgebraicSpace F hF)
variable [IsClosedImmersion i]

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.closedSubspaceDegreeKernel F hF i 0 :
  Subobject (deg.obj 0))
