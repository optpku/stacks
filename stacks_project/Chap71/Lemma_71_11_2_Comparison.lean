/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.RelativeProjBaseChangeData.toPullbackIso' :
    ∀ {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF),
    yoneda.obj (relativeProjOver g deg) ≅ functorPullback g F)

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- The representing scheme of a positive-degree relative projective chart. -/
abbrev degreeChartScheme {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :=
  AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z d

/-- The canonical inclusion of a positive-degree relative projective chart. -/
abbrev degreeChartImmersion {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :=
  AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z) d

/-- The open cover of relative Proj by its positive-degree charts. -/
abbrev relativeProjDegreeCover {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :=
  AlgebraicGeometry.RelativeProjFunctor.degreeCover (F := F_Z)

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
