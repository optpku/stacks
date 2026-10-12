/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal.Locality
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 37.20.5 (1): having locally Noetherian fibres and being normal is local
in the fppf topology on the target. -/
@[stacks 0393] #check
  (AlgebraicGeometry.LocallyNoetherianNormal.isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Normal) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)

/- Lemma 37.20.5 (2): having locally Noetherian fibres and being normal is local
in the smooth topology on the source. -/
@[stacks 0393] #check
  (AlgebraicGeometry.LocallyNoetherianNormal.isLocalAtSourceSmooth :
    MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Normal) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
