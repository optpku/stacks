/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Flat

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.30.4: the target-indexed fibre-dimension function of a flat
finite-presentation morphism of schemes is lower semicontinuous. -/
@[stacks 0D4H] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.lowerSemicontinuous_fiberDimension :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Scheme.Hom.FinitePresentation f],
      LowerSemicontinuous f.fiberDimension)
