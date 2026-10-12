/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locality

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianCohenMacaulay

/- Lemma 37.22.11 (1): having locally Noetherian fibres and being
Cohen--Macaulay is local at the target for the fppf precoverage. -/
@[stacks 045V] #check
  (AlgebraicGeometry.LocallyNoetherianCohenMacaulay.isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.CohenMacaulay :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)

/- Lemma 37.22.11 (2): having locally Noetherian fibres and being
Cohen--Macaulay is local at the source for the syntomic precoverage. -/
@[stacks 045V] #check
  (AlgebraicGeometry.LocallyNoetherianCohenMacaulay.isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.CohenMacaulay :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)

end AlgebraicGeometry.LocallyNoetherianCohenMacaulay
