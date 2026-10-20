/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.ClosedImmersion
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 82.4.3: Let `S` be a scheme. Let `i : Y ⟶ X` be a closed immersion of
algebraic spaces over `S`. Let `G` be a quasi-coherent `𝒪_Y`-module. Let `y ∈ |Y|`
with image `Points.map i y ∈ |X|`. Let `d : ℕ∞`. Then `G` has length `d` at `y` if
and only if `(pushforward i).obj G` has length `d` at `Points.map i y`. -/
@[stacks 0EE3] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.hasLengthAt_pushforward_closedImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (i : Y ⟶ X) [IsClosedImmersion i]
      (G : Y.Modules) [G.IsQuasicoherent] (y : Points Y) (d : ℕ∞),
      hasLengthAt G y d ↔ hasLengthAt ((pushforward i).obj G) (Points.map i y) d)
