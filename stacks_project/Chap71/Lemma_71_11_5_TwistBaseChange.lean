/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange.comparison :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X')}
    {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'} (hAlg : AlgebraPullback g deg deg')
    {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg'),
    GradedAlgebraComparison (CanonicalTwists.BaseChange.map g hAlg hF hF')
      (CanonicalTwists.family F hF) (CanonicalTwists.family F' hF'))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange.degreeIso :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X')}
    {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'} (hAlg : AlgebraPullback g deg deg')
    {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg'),
    ∀ n : ℤ,
    (Modules.pullback (CanonicalTwists.BaseChange.map g hAlg hF hF')).obj
      (CanonicalTwists.obj F hF n) ≅ CanonicalTwists.obj F' hF' n)

