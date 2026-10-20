/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Lifting
import StacksCheckRecall

/-!
# Étale-local lifting for smooth morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.19.7: A commutative square of algebraic spaces over a scheme with
smooth right arrow and a thickening on the left admits lifts after an étale
covering of the thickened space. -/
@[stacks 0CHJ] #check
  (AlgebraicGeometry.AlgebraicSpace.Smooth.exists_etaleCovering_lift :
    ∀ {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
      (f : X ⟶ Y) [Smooth f] (i : T ⟶ T') [IsThickening i]
      (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b),
      ∃ 𝒰 : etalePrecoverage.ZeroHypercover.{u} T',
        ∀ j : 𝒰.I₀, Smooth.LiftsAlong f i a b (𝒰.f j))
