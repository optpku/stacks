/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.EtaleCube
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

universe u

/- 81.6.5.1: A thickening–affine pushout admits a scheme presentation cube over any
prescribed surjective étale scheme atlas, with pushout front and back faces, cartesian
side faces, and surjective étale northeast arrows. -/
@[stacks 07W1] #check
  (AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening.exists_cube :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
      (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
      [IsThickening i] [Affine f], IsPushout i f i' g →
      ∀ {Y1 : Over S} (πY : ofOver Y1 ⟶ Y) [Etale πY] [Surjective πY],
        Nonempty (Cube i f i' g πY))
