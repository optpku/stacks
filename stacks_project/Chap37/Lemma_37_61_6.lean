/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Regular

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.61.6: A locally finite-type morphism of schemes with regular target is perfect. -/
@[stacks 068B] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isPerfect_of_regular :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Regular S] [AlgebraicGeometry.LocallyOfFiniteType f],
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f)
