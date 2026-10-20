module

public import stacks_project.Chap35.Lemma_35_15_2
public import ReasLib.AlgebraicGeometry.Scheme.ObjectProperty.AffineDescent
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ObjectProperty

/- Remark 35.15.3 (1): for smooth locality, descent along surjective affine
morphisms need only be assumed for standard smooth morphisms. -/
@[stacks 034A]
#check (AlgebraicGeometry.Scheme.ObjectProperty.standardSmoothLocalOfZariskiLocal :
  ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardSmooth ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
    P.IsLocal Scheme.bigSmoothPrecoverage)

/- Remark 35.15.3 (2): for syntomic locality, descent along surjective affine
morphisms need only be assumed for standard syntomic morphisms. -/
@[stacks 034A]
#check (AlgebraicGeometry.Scheme.ObjectProperty.standardSyntomicLocalOfZariskiLocal :
  ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardSyntomic ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
    P.IsLocal Scheme.bigSyntomicPrecoverage)

/- Remark 35.15.3 (3): for étale locality, descent along surjective affine
morphisms need only be assumed for standard étale morphisms. -/
@[stacks 034A]
#check (AlgebraicGeometry.Scheme.ObjectProperty.standardEtaleLocalOfZariskiLocal :
  ∀ (P : CategoryTheory.ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardEtale ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)],
    P.IsLocal Scheme.etalePrecoverage)

end AlgebraicGeometry.Scheme.ObjectProperty
