/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Normal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.20.3: a smooth morphism of schemes is normal. -/
@[stacks 056W] #check
  (AlgebraicGeometry.instNormalOfSmooth :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Smooth f],
      AlgebraicGeometry.Normal f)
