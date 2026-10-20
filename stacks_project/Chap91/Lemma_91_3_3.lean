/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.Cartesian
import StacksCheckRecall

/-!
# Strict morphisms of thickenings as cartesian squares

A morphism of thickenings of ringed spaces is strict precisely when its
commutative square is cartesian.
-/

open CategoryTheory

universe u

/- Lemma 91.3.3 In Situation 91.3.1, the morphism of thickenings
`(f, f') = (g.left, g.right)` is a strict morphism of thickenings if and only if
the commutative square 91.3.1.1 is cartesian in the category of ringed spaces. -/
@[stacks 08L2] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Hom.isStrict_iff_isPullback :
    ∀ {T U : AlgebraicGeometry.RingedSpace.Thickening.{u}} (g : T ⟶ U),
      Epi (AlgebraicGeometry.RingedSpace.Thickening.Hom.idealMap g) ↔
        IsPullback T.hom g.left g.right U.hom)
