/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
import StacksCheckRecall

/-!
# Étale universally injective morphisms of algebraic spaces are open immersions
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.51.2 -/
@[stacks 05W5] #check
  (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.of_etale_of_universallyInjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Etale f]
      [AlgebraicGeometry.AlgebraicSpace.UniversallyInjective f],
      AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion f)
