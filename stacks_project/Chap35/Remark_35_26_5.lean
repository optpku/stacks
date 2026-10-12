/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.MorphismProperty

/- Remark 35.26.5 (1): for smooth locality on the source, descent along surjective
affine morphisms need only be assumed for standard smooth morphisms. -/
@[stacks 036I] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.smoothLocalAtSourceOfStandardSmooth :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft (@Smooth : CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (AffineScheme.standardSmooth ⊓
          CategoryTheory.MorphismProperty.inverseImage
            (@Surjective : CategoryTheory.MorphismProperty Scheme.{u})
            AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.bigSmoothPrecoverage)

/- Remark 35.26.5 (2): for syntomic locality on the source, descent along surjective
affine morphisms need only be assumed for standard syntomic morphisms. -/
@[stacks 036I] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.syntomicLocalAtSourceOfStandardSyntomic :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft (@Syntomic : CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (AffineScheme.standardSyntomic ⊓
          CategoryTheory.MorphismProperty.inverseImage
            (@Surjective : CategoryTheory.MorphismProperty Scheme.{u})
            AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.bigSyntomicPrecoverage)

/- Remark 35.26.5 (3): for étale locality on the source, descent along surjective
affine morphisms need only be assumed for standard étale morphisms. -/
@[stacks 036I] #check
  (AlgebraicGeometry.Scheme.MorphismProperty.etaleLocalAtSourceOfStandardEtale :
    ∀ (P : CategoryTheory.MorphismProperty Scheme.{u})
      [P.RespectsLeft (@Etale : CategoryTheory.MorphismProperty Scheme.{u})]
      [IsZariskiLocalAtSource P]
      [IsZariskiLocalAtTarget P]
      [(P.inverseImage AffineScheme.forgetToScheme).HasOfPrecompProperty
        (AffineScheme.standardEtale ⊓
          CategoryTheory.MorphismProperty.inverseImage
            (@Surjective : CategoryTheory.MorphismProperty Scheme.{u})
            AffineScheme.forgetToScheme)],
      P.IsLocalAtSource Scheme.etalePrecoverage)

end AlgebraicGeometry.Scheme.MorphismProperty
