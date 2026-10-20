/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.MorphismProperty

/- Lemma 35.26.4 (1): a morphism property that ascends under flat precomposition,
is Zariski-local on the source and target, and descends under surjective flat
precomposition between affine schemes is local on the source for the fpqc precoverage. -/
@[stacks 036H] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.fpqcLocalAtSource :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft (@Flat : CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (CategoryTheory.MorphismProperty.inverseImage
          ((@Flat ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.fpqcPrecoverage)

/- Lemma 35.26.4 (2): a morphism property that ascends under flat, locally finitely
presented precomposition, is Zariski-local on the source and target, and descends under
surjective such precomposition between affine schemes is local on the source for fppf. -/
@[stacks 036H] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.fppfLocalAtSource :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft
        ((@Flat ⊓ @LocallyOfFinitePresentation) :
          CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (CategoryTheory.MorphismProperty.inverseImage
          ((@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective) :
            CategoryTheory.MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.fppfPrecoverage)

/- Lemma 35.26.4 (3): a morphism property that ascends under étale precomposition,
is Zariski-local on the source and target, and descends under surjective étale
precomposition between affine schemes is local on the source for the étale precoverage. -/
@[stacks 036H] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.etaleLocalAtSource :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft (@Etale : CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (CategoryTheory.MorphismProperty.inverseImage
          ((@Etale ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.etalePrecoverage)

/- Lemma 35.26.4 (4): a morphism property that ascends under smooth precomposition,
is Zariski-local on the source and target, and descends under surjective smooth
precomposition between affine schemes is local on the source for the smooth precoverage. -/
@[stacks 036H] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.smoothLocalAtSource :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft (@Smooth : CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (CategoryTheory.MorphismProperty.inverseImage
          ((@Smooth ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.bigSmoothPrecoverage)

/- Lemma 35.26.4 (5): a morphism property that ascends under syntomic precomposition,
is Zariski-local on the source and target, and descends under surjective syntomic
precomposition between affine schemes is local on the source for the syntomic precoverage. -/
@[stacks 036H] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.syntomicLocalAtSource :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft (@Syntomic : CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (CategoryTheory.MorphismProperty.inverseImage
          ((@Syntomic ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.bigSyntomicPrecoverage)

end AlgebraicGeometry.Scheme.MorphismProperty
