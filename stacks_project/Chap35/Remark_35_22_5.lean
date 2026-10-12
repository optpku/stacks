/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent
public import stacks_project.Chap35.Lemma_35_22_4
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineDescendsAlong

/- Remark 35.22.5 (1): affine descent along surjective standard smooth morphisms
suffices for locality on the target in the smooth topology. -/
@[stacks 034G]
#check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetSmoothOfStandardSmooth :
    ∀ (P : MorphismProperty Scheme.{u}),
      [IsZariskiLocalAtTarget P] →
      [P.IsStableUnderBaseChangeAgainst (@Smooth : MorphismProperty Scheme.{u})] →
      [AffineDescendsAlong P
        (AffineScheme.standardSmooth.map AffineScheme.forgetToScheme)] →
      P.IsLocalAtTarget Scheme.bigSmoothPrecoverage)

/- Remark 35.22.5 (2): affine descent along surjective standard syntomic morphisms
suffices for locality on the target in the syntomic topology. -/
@[stacks 034G]
#check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetSyntomicOfStandardSyntomic :
    ∀ (P : MorphismProperty Scheme.{u}),
      [IsZariskiLocalAtTarget P] →
      [P.IsStableUnderBaseChangeAgainst (@Syntomic : MorphismProperty Scheme.{u})] →
      [AffineDescendsAlong P
        (AffineScheme.standardSyntomic.map AffineScheme.forgetToScheme)] →
      P.IsLocalAtTarget Scheme.bigSyntomicPrecoverage)

/- Remark 35.22.5 (3): affine descent along surjective standard étale morphisms
suffices for locality on the target in the étale topology. -/
@[stacks 034G]
#check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetEtaleOfStandardEtale :
    ∀ (P : MorphismProperty Scheme.{u}),
      [IsZariskiLocalAtTarget P] →
      [P.IsStableUnderBaseChangeAgainst (@Etale : MorphismProperty Scheme.{u})] →
      [AffineDescendsAlong P
        (AffineScheme.standardEtale.map AffineScheme.forgetToScheme)] →
      P.IsLocalAtTarget Scheme.etalePrecoverage)

end AlgebraicGeometry.AffineDescendsAlong
