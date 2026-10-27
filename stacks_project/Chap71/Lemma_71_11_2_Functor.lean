/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.baseMap_relativelyRepresentable :
    ∀ (F : ProjFunctor X 𝒜)
    (deg : DegreePieces 𝒜) (hF : F.IsAssociatedToQuadruples deg),
    yoneda.relativelyRepresentable F.baseMap)
