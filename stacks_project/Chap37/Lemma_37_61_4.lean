/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.61.4: A composition of perfect morphisms of schemes is perfect. -/
@[stacks 0689] #check (
  AlgebraicGeometry.LocallyOfType.isPerfectRingMap_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f]
      [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap g],
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap (f ≫ g))
