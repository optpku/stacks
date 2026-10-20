/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Locality

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianGorenstein

/- Lemma 48.25.12 (1): having locally Noetherian fibres and being Gorenstein is
local at the target for the fppf precoverage. -/
@[stacks 0C0A] #check
  (AlgebraicGeometry.LocallyNoetherianGorenstein.isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.Gorenstein :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)

/- Lemma 48.25.12 (2): having locally Noetherian fibres and being Gorenstein is
local at the source for the syntomic precoverage. -/
@[stacks 0C0A] #check
  (AlgebraicGeometry.LocallyNoetherianGorenstein.isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓
          (@AlgebraicGeometry.Gorenstein :
            MorphismProperty AlgebraicGeometry.Scheme.{u})) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)

end AlgebraicGeometry.LocallyNoetherianGorenstein
