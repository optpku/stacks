/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalBaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.canonicalBaseChangeIso :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X')}
    {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'} (hAlg : AlgebraPullback g deg deg')
    {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg'),
    toAlgebraicSpace F' hF' ≅ fibreProduct g hF)

