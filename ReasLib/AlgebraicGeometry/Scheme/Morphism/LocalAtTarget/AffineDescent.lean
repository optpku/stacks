/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineScheme.StandardMorphisms
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.StandardRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic.StandardRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineDescendsAlong

variable (P : MorphismProperty Scheme.{u})

/-- A Zariski-local morphism property stable under flat base change and affine fpqc
descent is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst (@Flat : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P (@Flat : MorphismProperty Scheme.{u})] :
    P.IsLocalAtTarget Scheme.fpqcPrecoverage := sorry

/-- A Zariski-local morphism property stable under flat, locally finitely presented base
change and affine fppf descent is local on the target for the fppf precoverage. -/
instance isLocalAtTargetFppf
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})] :
    P.IsLocalAtTarget Scheme.fppfPrecoverage := sorry

/-- A Zariski-local morphism property stable under étale base change and affine étale
descent is local on the target for the étale precoverage. -/
instance isLocalAtTargetEtale
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P (@Etale : MorphismProperty Scheme.{u})] :
    P.IsLocalAtTarget Scheme.etalePrecoverage := sorry

/-- A Zariski-local morphism property stable under smooth base change and affine smooth
descent is local on the target for the smooth precoverage. -/
instance isLocalAtTargetSmooth
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst (@Smooth : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P (@Smooth : MorphismProperty Scheme.{u})] :
    P.IsLocalAtTarget Scheme.bigSmoothPrecoverage := sorry

/-- A Zariski-local morphism property stable under syntomic base change and affine syntomic
descent is local on the target for the syntomic precoverage. -/
instance isLocalAtTargetSyntomic
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst (@Syntomic : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P (@Syntomic : MorphismProperty Scheme.{u})] :
    P.IsLocalAtTarget Scheme.bigSyntomicPrecoverage := sorry

/-- A Zariski-local morphism property stable under smooth base change and admitting affine
descent along standard smooth morphisms is local on the target for the smooth precoverage. -/
instance isLocalAtTargetSmoothOfStandardSmooth
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst (@Smooth : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P
      (AffineScheme.standardSmooth.map AffineScheme.forgetToScheme)] :
    P.IsLocalAtTarget Scheme.bigSmoothPrecoverage := sorry

/-- A Zariski-local morphism property stable under syntomic base change and admitting affine
descent along standard syntomic morphisms is local on the target for the syntomic precoverage. -/
instance isLocalAtTargetSyntomicOfStandardSyntomic
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst (@Syntomic : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P
      (AffineScheme.standardSyntomic.map AffineScheme.forgetToScheme)] :
    P.IsLocalAtTarget Scheme.bigSyntomicPrecoverage := sorry

/-- A Zariski-local morphism property stable under étale base change and admitting affine
descent along standard étale morphisms is local on the target for the étale precoverage. -/
instance isLocalAtTargetEtaleOfStandardEtale
    [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})]
    [AffineDescendsAlong P
      (AffineScheme.standardEtale.map AffineScheme.forgetToScheme)] :
    P.IsLocalAtTarget Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.AffineDescendsAlong
