/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AffineScheme.StandardMorphisms
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.MorphismProperty

variable (P : CategoryTheory.MorphismProperty Scheme.{u})

/-- A morphism property that ascends under flat precomposition, is Zariski-local on the
source and target, and descends under surjective flat precomposition between affine schemes
is local on the source for the fpqc precoverage. -/
instance fpqcLocalAtSource
    [P.RespectsLeft (@Flat : CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (CategoryTheory.MorphismProperty.inverseImage
        ((@Flat ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.fpqcPrecoverage := sorry

/-- A morphism property that ascends under flat, locally finitely presented precomposition,
is Zariski-local on the source and target, and descends under surjective such precomposition
between affine schemes is local on the source for the fppf precoverage. -/
instance fppfLocalAtSource
    [P.RespectsLeft
      ((@Flat ⊓ @LocallyOfFinitePresentation) :
        CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (CategoryTheory.MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective) :
          CategoryTheory.MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.fppfPrecoverage := sorry

/-- A morphism property that ascends under étale precomposition, is Zariski-local on the
source and target, and descends under surjective étale precomposition between affine schemes
is local on the source for the étale precoverage. -/
instance etaleLocalAtSource
    [P.RespectsLeft (@Etale : CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (CategoryTheory.MorphismProperty.inverseImage
        ((@Etale ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.etalePrecoverage := sorry

/-- A morphism property that ascends under smooth precomposition, is Zariski-local on the
source and target, and descends under surjective smooth precomposition between affine schemes
is local on the source for the smooth precoverage. -/
instance smoothLocalAtSource
    [P.RespectsLeft (@Smooth : CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (CategoryTheory.MorphismProperty.inverseImage
        ((@Smooth ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.bigSmoothPrecoverage := sorry

/-- A morphism property that ascends under syntomic precomposition, is Zariski-local on the
source and target, and descends under surjective syntomic precomposition between affine
schemes is local on the source for the syntomic precoverage. -/
instance syntomicLocalAtSource
    [P.RespectsLeft (@Syntomic : CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (CategoryTheory.MorphismProperty.inverseImage
        ((@Syntomic ⊓ @Surjective) : CategoryTheory.MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.bigSyntomicPrecoverage := sorry

/-- A morphism property that ascends under smooth precomposition, is Zariski-local on the
source and target, and descends under surjective standard smooth precomposition between
affine schemes is local on the source for the smooth precoverage. -/
instance smoothLocalAtSourceOfStandardSmooth
    [P.RespectsLeft (@Smooth : CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (AffineScheme.standardSmooth ⊓
        CategoryTheory.MorphismProperty.inverseImage
          (@Surjective : CategoryTheory.MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.bigSmoothPrecoverage := sorry

/-- A morphism property that ascends under syntomic precomposition, is Zariski-local on the
source and target, and descends under surjective standard syntomic precomposition between
affine schemes is local on the source for the syntomic precoverage. -/
instance syntomicLocalAtSourceOfStandardSyntomic
    [P.RespectsLeft (@Syntomic : CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (AffineScheme.standardSyntomic ⊓
        CategoryTheory.MorphismProperty.inverseImage
          (@Surjective : CategoryTheory.MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.bigSyntomicPrecoverage := sorry

/-- A morphism property that ascends under étale precomposition, is Zariski-local on the
source and target, and descends under surjective standard étale precomposition between
affine schemes is local on the source for the étale precoverage. -/
instance etaleLocalAtSourceOfStandardEtale
    [P.RespectsLeft (@Etale : CategoryTheory.MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P]
    [IsZariskiLocalAtTarget P]
    [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
      (AffineScheme.standardEtale ⊓
        CategoryTheory.MorphismProperty.inverseImage
          (@Surjective : CategoryTheory.MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocalAtSource Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.MorphismProperty
