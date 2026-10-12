/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 35.32.6: a scheme-morphism property that is étale local on the source and target
and stable under postcomposition by open immersions is étale local on source-and-target. -/
@[stacks 04R2]
#check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.of_isLocalAtSource_isLocalAtTarget :
    ∀ (P : MorphismProperty AlgebraicGeometry.Scheme.{u})
      [P.IsLocalAtSource AlgebraicGeometry.Scheme.etalePrecoverage]
      [P.IsLocalAtTarget AlgebraicGeometry.Scheme.etalePrecoverage]
      [P.RespectsRight
        (@AlgebraicGeometry.IsOpenImmersion :
          MorphismProperty AlgebraicGeometry.Scheme.{u})],
      AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P)
