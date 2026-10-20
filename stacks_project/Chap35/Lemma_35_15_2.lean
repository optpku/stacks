/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap35.Definition_35_15_1
public import ReasLib.AlgebraicGeometry.Scheme.ObjectProperty.AffineDescent
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ObjectProperty

/- Lemma 35.15.2 (1): a Zariski-local property that ascends along flat morphisms
of affine schemes and descends along surjective flat morphisms of affine schemes is
local for the fpqc precoverage. -/
@[stacks 0349] #check
  (AlgebraicGeometry.Scheme.ObjectProperty.fpqcLocalOfZariskiLocal :
    ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
      [P.IsLocal Scheme.zariskiPrecoverage]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
        (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
        (MorphismProperty.inverseImage
          ((@Flat ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)],
      P.IsLocal Scheme.fpqcPrecoverage)

/- Lemma 35.15.2 (2): a Zariski-local property that ascends along flat, locally
finitely presented morphisms of affine schemes and descends along their surjective members
is local for the fppf precoverage. -/
@[stacks 0349] #check
  (AlgebraicGeometry.Scheme.ObjectProperty.fppfLocalOfZariskiLocal :
    ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
      [P.IsLocal Scheme.zariskiPrecoverage]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
        (MorphismProperty.inverseImage
          ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
        (MorphismProperty.inverseImage
          ((@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective) : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
      P.IsLocal Scheme.fppfPrecoverage)

/- Lemma 35.15.2 (3): a Zariski-local property that ascends along étale morphisms
of affine schemes and descends along surjective étale morphisms of affine schemes is
local for the étale precoverage. -/
@[stacks 0349] #check
  (AlgebraicGeometry.Scheme.ObjectProperty.etaleLocalOfZariskiLocal :
    ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
      [P.IsLocal Scheme.zariskiPrecoverage]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
        (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
        (MorphismProperty.inverseImage
          ((@Etale ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)],
      P.IsLocal Scheme.etalePrecoverage)

/- Lemma 35.15.2 (4): a Zariski-local property that ascends along smooth morphisms
of affine schemes and descends along surjective smooth morphisms of affine schemes is
local for the smooth precoverage. -/
@[stacks 0349] #check
  (AlgebraicGeometry.Scheme.ObjectProperty.smoothLocalOfZariskiLocal :
    ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
      [P.IsLocal Scheme.zariskiPrecoverage]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
        (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
        (MorphismProperty.inverseImage
          ((@Smooth ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)],
      P.IsLocal Scheme.bigSmoothPrecoverage)

/- Lemma 35.15.2 (5): a Zariski-local property that ascends along syntomic morphisms
of affine schemes and descends along surjective syntomic morphisms of affine schemes is
local for the syntomic precoverage. -/
@[stacks 0349] #check
  (AlgebraicGeometry.Scheme.ObjectProperty.syntomicLocalOfZariskiLocal :
    ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
      [P.IsLocal Scheme.zariskiPrecoverage]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
        (MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)]
      [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
        (MorphismProperty.inverseImage
          ((@Syntomic ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)],
      P.IsLocal Scheme.bigSyntomicPrecoverage)

end AlgebraicGeometry.Scheme.ObjectProperty
