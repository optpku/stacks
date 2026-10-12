/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.22.4 (1): a Zariski-local morphism property stable under flat base
change and affine fpqc descent is local on the target for the fpqc precoverage. -/
@[stacks 02KP] #check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetFpqc :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsZariskiLocalAtTarget P]
      [P.IsStableUnderBaseChangeAgainst
        (@AlgebraicGeometry.Flat :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})]
      [AlgebraicGeometry.AffineDescendsAlong P
        (@AlgebraicGeometry.Flat :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})],
      P.IsLocalAtTarget AlgebraicGeometry.Scheme.fpqcPrecoverage)

/- Lemma 35.22.4 (2): a Zariski-local morphism property stable under flat,
locally finitely presented base change and affine fppf descent is local on the
target for the fppf precoverage. -/
@[stacks 02KP] #check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetFppf :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsZariskiLocalAtTarget P]
      [P.IsStableUnderBaseChangeAgainst
        ((@AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation) :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})]
      [AlgebraicGeometry.AffineDescendsAlong P
        ((@AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation) :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})],
      P.IsLocalAtTarget AlgebraicGeometry.Scheme.fppfPrecoverage)

/- Lemma 35.22.4 (3): a Zariski-local morphism property stable under étale base
change and affine étale descent is local on the target for the étale precoverage. -/
@[stacks 02KP] #check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetEtale :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsZariskiLocalAtTarget P]
      [P.IsStableUnderBaseChangeAgainst
        (@AlgebraicGeometry.Etale :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})]
      [AlgebraicGeometry.AffineDescendsAlong P
        (@AlgebraicGeometry.Etale :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})],
      P.IsLocalAtTarget AlgebraicGeometry.Scheme.etalePrecoverage)

/- Lemma 35.22.4 (4): a Zariski-local morphism property stable under smooth base
change and affine smooth descent is local on the target for the smooth precoverage. -/
@[stacks 02KP] #check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetSmooth :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsZariskiLocalAtTarget P]
      [P.IsStableUnderBaseChangeAgainst
        (@AlgebraicGeometry.Smooth :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})]
      [AlgebraicGeometry.AffineDescendsAlong P
        (@AlgebraicGeometry.Smooth :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})],
      P.IsLocalAtTarget AlgebraicGeometry.Scheme.bigSmoothPrecoverage)

/- Lemma 35.22.4 (5): a Zariski-local morphism property stable under syntomic base
change and affine syntomic descent is local on the target for the syntomic precoverage. -/
@[stacks 02KP] #check
  (AlgebraicGeometry.AffineDescendsAlong.isLocalAtTargetSyntomic :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsZariskiLocalAtTarget P]
      [P.IsStableUnderBaseChangeAgainst
        (@AlgebraicGeometry.Syntomic :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})]
      [AlgebraicGeometry.AffineDescendsAlong P
        (@AlgebraicGeometry.Syntomic :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})],
      P.IsLocalAtTarget AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
