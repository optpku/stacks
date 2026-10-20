/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Thickening

open AlgebraicGeometry CategoryTheory

universe u

/- Theorem 41.15.1: if `S₀ ⟶ S` is a thickening and `X` is étale over `S`, then
base change induces a bijection from `S`-morphisms `Y ⟶ X` to `S₀`-morphisms between
their pullbacks. -/
@[stacks 025H] #check
  (AlgebraicGeometry.Etale.overPullbackMap_bijective_of_isThickening :
    ∀ {S₀ S : Scheme.{u}} (i : S₀ ⟶ S) [IsThickening i]
      (X Y : Over S) [Etale X.hom],
      Function.Bijective (fun f : Y ⟶ X ↦ (Over.pullback i).map f))
