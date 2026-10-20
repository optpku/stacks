/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Smooth
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.61.8: if `g : Y ⟶ S` is smooth and `f ≫ g : X ⟶ S` is perfect,
then `f : X ⟶ Y` is perfect. -/
@[stacks 068D] #check
  (AlgebraicGeometry.LocallyOfType.isPerfectRingMap_of_smooth_of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.Smooth g]
      [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap (f ≫ g)],
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f)
