/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.UniversalHomeomorphism

open CategoryTheory
open AlgebraicGeometry

universe u

/- Theorem 59.45.1: for a universal homeomorphism `i : S' ⟶ S`, base change
induces a bijection on morphisms into an étale scheme over `S`. -/
@[stacks 0BTY] #check
  (AlgebraicGeometry.Etale.overPullbackMap_bijective_of_universalHomeomorphism :
    ∀ {S' S : Scheme.{u}} (i : S' ⟶ S) [UniversalHomeomorphism i]
      (X Y : Over S) [Etale X.hom],
      Function.Bijective (fun g : Y ⟶ X ↦ (Over.pullback i).map g))
